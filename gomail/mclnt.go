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
	NGO=10
	NUSER=100
	NMSG=10
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
	fmt.Printf("pickup %s\n", u)
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

func smtp_client(c int) {
	for i := 0; i < (NMSG * NUSER) / NGO; i++ {
		u := (i+c) % NUSER
		sendmail("u" + strconv.Itoa(u))
	}
}

func pop_client(c int) {
	fmt.Printf("pop clnt %d\n", c)
	n := NUSER/NGO
	o := c * n
	for u := 0; u < n; u++ {
		pickup("u" + strconv.Itoa(u+o))
	}
}

func measure(s string, f func(int)) {
	var wg sync.WaitGroup
	start := time.Now()
	wg.Add(NGO)
	for c := 0; c < NGO; c++ {
		go func (c int) {
			defer wg.Done()
			f(c)
		}(c)
	}
	wg.Wait()
	t := time.Now()
	elapsed := t.Sub(start)
	fmt.Printf("%s: time %v\n", s, elapsed)
}

func main() {
	if len(os.Args) != 3 {
		panic("<smtp> <pop>")
	}
	var wg sync.WaitGroup
	wg.Add(2)
	go func () {
		defer wg.Done()
		if os.Args[1] == "1" {
			measure("smtp", smtp_client)
		}
	}()
	go func () {
		defer wg.Done()
		if os.Args[2] == "1" {
			measure("pop", pop_client)
		}
	}()
	wg.Wait()
}
