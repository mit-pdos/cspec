package main

// use: $ time go run mclnt.go

import (
	"fmt"
	"log"
	"net/smtp"
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

	// Send the QUIT command and close the connection.
	err = c.Quit()
	if err != nil {
		log.Fatal(err)
	}
}

func main() {
	for i := 0; i < 10000; i++ {
		sendmail("u1")
	}
}
