package main

import (
	"bufio"
	"bytes"
	"crypto/md5"
	"encoding/hex"
	"fmt"
	"log"
	"net"
	"net/textproto"
	"os"
	"strings"
)

// A go mail server that is equivalent to the Gallina/Haskell version, handling
// postal.  Set GOPATH to 6.826-labs/gomail, and run server by typing "go run
// gomail.go".

const dir = "/tmp/mailtest"

type Message struct {
	Client string
	From string
	To string
	Data []string
}

func reply(c net.Conn, format string, elems ...interface{}) {
	var err error
	s := fmt.Sprintf(format, elems...)
	b := []byte(s + "\r\n")
	_, err = c.Write(b)
	if err != nil {
		log.Fatal(err)
	}
}

func (msg *Message) process_msg() error {
	// fmt.Printf("process msg %v\n", msg)
	hasher := md5.New()

	var buffer bytes.Buffer
	for _, s := range msg.Data {
           buffer.WriteString(s)
	}
	b := []byte(buffer.String())
	hasher.Write(b)
	name := hex.EncodeToString(hasher.Sum(nil))
	tpn := dir+"/" + msg.To + "/tmp/"+name
	file, err := os.Create(tpn)
	if err != nil {
		return err
	}
	_, err = file.Write(b)
	if err != nil {
		return err
	}
	file.Close()
	fpn := dir+"/" + msg.To + "/mail/"+name
	err = os.Rename(tpn,fpn)
	if err != nil {
		return err
	}
	return nil
}

func process_data(tp *textproto.Reader) (error, []string) {
	lines, err := tp.ReadDotLines()
	if err != nil {
		return err, nil
	}
	return nil, lines
}

func process_smtp(c net.Conn) {
	reader := bufio.NewReader(c)
	tp := textproto.NewReader(reader)
	var msg *Message

	reply(c, "220 Ready")
	for {
		line, err := tp.ReadLine()
		if err != nil {
			reply(c, "500 Error")
			break
		}
		words := strings.Fields(line)
		// fmt.Printf("msg: %v\n", words)
		if len(words) <= 0 {
			break
		}
		switch words[0] {
		case "HELO":
			msg = &Message{}
			reply(c, "250 OK")
		case "EHLO":
			msg = &Message{}
			reply(c, "250 OK")
		case "MAIL":
			reply(c, "250 OK")
		case "RCPT":
			if len(words) < 2 || msg == nil {
				reply(c, "500 incorrect RCPT or no HELO")
				break
			}
			u := strings.Split(words[1], ":")
			if len(u) < 2 {
				reply(c, "500 No user")
				break
			}
			u[1] = strings.Replace(u[1], "<", "", -1)
			u[1] = strings.Replace(u[1], ">", "", -1)
			msg.To = u[1]
			reply(c, "250 OK")
		case "DATA":
			reply(c, "354 Proceed with data")
			err, lines := process_data(tp)
			if err != nil || msg == nil {
				reply(c, "500 Error process_data")
				break
			}
			msg.Data = lines
			err = msg.process_msg()
			if err != nil {
				reply(c, "500 Error process_msg")
				break
			} else {
				reply(c, "250 OK")
			}
	        case "QUIT":
			reply(c, "221 Bye")
			break
		default:
			log.Printf("Unknown command %v", words)
			reply(c, "500 Error")
			break
		}
		
	}	
}

func main() {
	conn, err := net.Listen("tcp", "localhost:2525")
	if err != nil {
		log.Fatal(err)
	}
	defer conn.Close()
	for {
		nc, err := conn.Accept()
		if err == nil {
			go process_smtp(nc)
		}
	}
}
