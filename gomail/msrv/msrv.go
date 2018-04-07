package main

import (
	"bufio"
	"bytes"
	"io/ioutil"
	"fmt"
	"log"
	"net"
	"net/textproto"
	"os"
	"strconv"
	"strings"
	"syscall"
	"time"
)

// A go mail server that is equivalent to the Gallina/Haskell version, handling
// postal.  Set GOPATH to 6.826-labs/gomail, and run server by typing "go run
// gomail.go".

const dir = "/dev/shm/mailtest"

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
	defer c.Close()
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

func smtp() {
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

type mailbox struct  {
	u string
	files []os.FileInfo
}

func mkMailbox(u string) (*mailbox, error) {
	mbox := &mailbox{u: u}
	fd, err := syscall.Open(mbox.pn(), os.O_RDONLY, 0755)
	if err != nil {
		return nil, err
	}
	err = syscall.Flock(fd, 2)
	if err != nil {
		return nil, err
	}
	mbox.files, err = ioutil.ReadDir(mbox.pn())
	_ = syscall.Flock(fd, 8)
	syscall.Close(fd)
	return mbox, err
}

func (mbox *mailbox) pn() string {
	return dir + "/" + mbox.u + "/mail/"
}

func (mbox *mailbox) file(words []string) (*os.FileInfo, bool) {
	if len(words) < 2 {
		return nil, false
	}
	i, err := strconv.Atoi(words[1])
	if err != nil {
		return nil, false
	}
	if len(mbox.files) < i+1 {
		return nil, false
	}
	return &mbox.files[i], true
}

func (mbox *mailbox) retr(file *os.FileInfo) ([]byte, error) {
	n := mbox.pn() + (*file).Name()
	f, err := os.Open(n)
	if err != nil {
		return nil, err
	}
	data := make([]byte, (*file).Size())
	_, err = f.Read(data)
	if err != nil {
		return nil, err
	}
	f.Close()
	return data, nil
}

func (mbox *mailbox) dele(file *os.FileInfo) error {
	fd, err := syscall.Open(mbox.pn(), os.O_RDONLY, 0755)
	if err != nil {
		return err
	}
	err = syscall.Flock(fd, 2)
	if err != nil {
		return err
	}

	n := mbox.pn() + (*file).Name()
	err = os.Remove(n)
	_ = syscall.Flock(fd, 8)
	syscall.Close(fd)
	return err
}


func send_data(tw *textproto.Writer, data []byte) bool {
	tw.PrintfLine("+OK")
	dwr := tw.DotWriter()
	_, err := dwr.Write(data)
	if err != nil {
		return false
	}
	err = dwr.Close()
	if err != nil {
		return false
	}
	return true
}

func process_pop(c net.Conn, tid int) {
	defer c.Close()
	
	reader := bufio.NewReader(c)
	tr := textproto.NewReader(reader)
	writer := bufio.NewWriter(c)
	tw := textproto.NewWriter(writer)
	var mbox *mailbox
	
	tw.PrintfLine("+OK")
	
	for {
		line, err := tr.ReadLine()
		if err != nil {
			tw.PrintfLine("-ERR")
			break
		}

		words := strings.Fields(line)
		// fmt.Printf("msg: %v\n", words)
		if len(words) <= 0 {
			tw.PrintfLine("-ERR")
			break
		}

		switch words[0] {
		case "USER":
			if len(words) < 2 {
				tw.PrintfLine("-ERR")
				break
			}
			mbox, err = mkMailbox(words[1])
			if err != nil {
				tw.PrintfLine("-ERR readdir")
				break
			}
			tw.PrintfLine("+OK")
		case "LIST":
			if mbox == nil {
				tw.PrintfLine("-ERR readdir")
				break
			}
			tw.PrintfLine("+OK")
			// d := tw.DotWriter()
			for i, file := range mbox.files {
				tw.PrintfLine("%d %d", i, file.Size())
			}
			tw.PrintfLine(".")
			tw.PrintfLine("+OK")
		case "RETR":
			if mbox == nil {
				tw.PrintfLine("-ERR mbox")
				break
			}
			file, ok := mbox.file(words)
			if !ok {
				tw.PrintfLine("-ERR file")
				break
			}
			b, err := mbox.retr(file)
			if err != nil {
				tw.PrintfLine("-ERR file")
				break
			}
			ok = send_data(tw, b)
			if !ok {
				tw.PrintfLine("-ERR data")
				break
			}
	        case "DELE":
			if mbox == nil {
				tw.PrintfLine("-ERR mbox")
				break
			}
			file, ok := mbox.file(words)
			if !ok {
				tw.PrintfLine("-ERR file %v")
				break
			}
			mbox.dele(file)
			if err != nil {
				tw.PrintfLine("-ERR remove")
				break
			}
			tw.PrintfLine("+OK")
		case "QUIT":
			tw.PrintfLine("+OK")
			break
	        default:
			tw.PrintfLine("-ERR")
			break
		}
	}
}


func pop() {
	conn, err := net.Listen("tcp", "localhost:2110")
	if err != nil {
		log.Fatal(err)
	}
	defer conn.Close()
	for c := 0;  ; c++ {
		nc, err := conn.Accept()
		if err == nil {
			go process_pop(nc, c)
		}
	}
}


func main() {
	go smtp()
	pop()
}
