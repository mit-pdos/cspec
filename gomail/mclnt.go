package main

// use: $ time go run mclnt.go

import (
	"bufio"
	"fmt"
	"log"
	"net"
	"net/smtp"
	"net/textproto"
	"strconv"
	"sync"
	"os"
	"strings"
	"time"
)

const (
	NUSER=100
	NMSG=1000
)

func sendmail(u string) {
	c, err := smtp.Dial("localhost:2525")
	if err != nil {
		log.Fatal(err)
	}

	if err := c.Hello("localhost"); err != nil {
		log.Fatal(err)
	}

	if err := c.Rcpt(u); err != nil {
		log.Fatal(err)
	}

	wc, err := c.Data()
	if err != nil {
		log.Fatal(err)
	}
	_, err = fmt.Fprintf(wc, "This is the email body")
	if err != nil {
		log.Fatal(err)
	}
	err = wc.Close()
	if err != nil {
		log.Fatal(err)
	}

	err = c.Quit()
	if err != nil {
		log.Fatal(err)
	}
}

func read_ok(tr *textproto.Reader) {
	line, err := tr.ReadLine()
	if err != nil {
		log.Fatal(err)
	}
	// fmt.Printf("line %s\n", line)
	if strings.HasPrefix(line, "+OK ") {
		return
	}
	log.Fatal("no +OK")
}

func read_lines(tr *textproto.Reader) []string {
	lines, err := tr.ReadDotLines()
	if err != nil {
		log.Fatal(err)
	}
	return lines
}

func pickup(u string) {
	c, err := net.Dial("tcp", "localhost:2110")
	if err != nil {
		log.Fatal(err)
	}
	defer c.Close()
	
	reader := bufio.NewReader(c)
	writer := bufio.NewWriter(c)
	tr := textproto.NewReader(reader)
	tw := textproto.NewWriter(writer)

	read_ok(tr)
	
	tw.PrintfLine("USER %s", u)
	read_ok(tr)
	
	tw.PrintfLine("LIST")
	read_ok(tr)

	lines := read_lines(tr)
	fmt.Printf("user %v lines %v\n", u, lines)
	for i := 0; i < len(lines); i++ {
		msg := strings.Fields(lines[i])
		tw.PrintfLine("RETR %s", msg[0])
		read_ok(tr)
		read_lines(tr)

		tw.PrintfLine("DELE %s", msg[0])
		read_ok(tr)
	}

	tw.PrintfLine("QUIT")
	read_ok(tr)
}

func clients(nclient int, f func (u string), b string) {
	var wg sync.WaitGroup
	wg.Add(nclient)
	start := time.Now()
	for t := 0; t < nclient; t++ {
		go func () {
			defer wg.Done()
			for i := 0; i < NMSG; i++ {
				u := i % NUSER
				f("u" + strconv.Itoa(u))
			}
		}()
	}
	wg.Wait()
	t := time.Now()
	elapsed := t.Sub(start)
	tput := float64(nclient*NMSG) / elapsed.Seconds()
	fmt.Printf("%s: time %v #msgs %v tput %v\n", b, elapsed, nclient * NMSG, tput)
}

func main() {
	if len(os.Args) != 3 {
		panic("<nclient smtp> <nclient pop>")
	}
	nsmtp, err := strconv.Atoi(os.Args[1])
	if err != nil {
		log.Fatal(err)
	}
	npop, err := strconv.Atoi(os.Args[2])
	if err != nil {
		log.Fatal(err)
	}
	var wg sync.WaitGroup
	wg.Add(2)
	go func () {
		defer wg.Done()
		clients(nsmtp, sendmail, "deliver")
	}()
	go func () {
		defer wg.Done()
		clients(npop, pickup, "pickup")
	}()
	wg.Wait()
}
