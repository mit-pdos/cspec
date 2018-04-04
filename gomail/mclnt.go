package main

// use: $ time go run mclnt.go

import (
	"fmt"
	"log"
	"net/smtp"
	"strconv"
	"sync"
	"os"
	"time"
)

const (
	NUSER=100
	NMSG=10000
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

	// Send the email body.
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

func main() {
	if len(os.Args) != 2 {
		panic("<nclient>")
	}
	nclient, err := strconv.Atoi(os.Args[1])
	if err != nil {
		log.Fatal(err)
	}
	var wg sync.WaitGroup
	wg.Add(nclient)
	start := time.Now()
	for t := 0; t < nclient; t++ {
		go func () {
			defer wg.Done()
			for i := 0; i < NMSG; i++ {
				u := NMSG % NUSER
				sendmail("u" + strconv.Itoa(u))
			}
		}()
	}
	wg.Wait()
	t := time.Now()
	elapsed := t.Sub(start)
	tput := float64(nclient*NMSG) / elapsed.Seconds()
	fmt.Printf("time %v #msgs %v tput %v\n", elapsed, nclient * NMSG, tput)
}
