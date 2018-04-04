package main

import (
	"bufio"
	"bytes"
	"fmt"
	"log"
	"net"
	"net/textproto"
	"os"
	"strconv"
	"strings"
	"time"
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

func (msg *Message) process_msg(tid int) error {
	// fmt.Printf("process msg %v tid %v\n", msg, tid)

	tpn := dir+"/" + msg.To + "/tmp/" + strconv.Itoa(tid)
	file, err := os.Create(tpn)
	if err != nil {
		return err
	}
	var buffer bytes.Buffer
	for _, s := range msg.Data {
		buffer.WriteString(s)
	}
	b := []byte(buffer.String())
	_, err = file.Write(b)
	if err != nil {
		return err
	}
	file.Close()

	for {
		fpn := dir+"/" + msg.To + "/mail/" + strconv.FormatInt(time.Now().UnixNano(), 16)
		err = os.Link(tpn, fpn)
		if err == nil {
			break
		}
		if os.IsExist(err) {
			fmt.Printf("retry link\n")
		} else {
			return err
		}
	}
	
	err = os.Remove(tpn)
	if err != nil {
		log.Fatalf("Unlink error %v\n", err)
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

func process_smtp(c net.Conn, tid int) {
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
			err = msg.process_msg(tid)
			if err != nil {
				fmt.Printf("err %v\n", err)
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
	for c := 0;  ; c++ {
		nc, err := conn.Accept()
		if err == nil {
			go process_smtp(nc, c)
		}
	}
}
