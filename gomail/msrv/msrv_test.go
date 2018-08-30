package main

import (
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"sync"
	"testing"
	"time"
)

const (
	NUSER = 100
)

func do_bench_loop(tid int, msg string, niter int, nsmtpiter int, npopiter int) error {
	r := rand.New(rand.NewSource(time.Now().UnixNano()))
	for l := 0; l < niter; l++ {
		for i := 0; i < nsmtpiter; i++ {
			u := "u" + strconv.Itoa(r.Int()%NUSER)
			if validUser(u) {
				m := &Message{To: u, Data: []string{msg}}
				err := m.process_msg(tid)
				if err != nil {
					return err
				}
			} else {
				return fmt.Errorf("Invalid user %v", u)
			}
		}
		for i := 0; i < npopiter; i++ {
			u := "u" + strconv.Itoa(r.Int()%NUSER)
			if validUser(u) {
				mbox, err := mkMailbox(u)
				if err != nil {
					return err
				}
				for _, f := range mbox.files {
					_, err = mbox.retr(&f)
					if err != nil {
						return err
					}
				}

				mbox.unlock()

				for _, f := range mbox.files {
					err = mbox.dele(&f)
					if err != nil {
						// benchmark artifact; matches cmail/haskell
						// return err
					}
				}
			} else {
				return fmt.Errorf("Invalid user %v", u)
			}
		}
	}
	return nil
}

func TestMixedLoad(t *testing.T) {
	nprocEnv := os.Getenv("GOMAIL_NPROC")
	nproc64, err := strconv.ParseInt(nprocEnv, 10, 64)
	if err != nil {
		t.Fatal(err)
	}

	niterEnv := os.Getenv("GOMAIL_NITER")
	niter64, err := strconv.ParseInt(niterEnv, 10, 64)
	if err != nil {
		t.Fatal(err)
	}

	nproc := int(nproc64)
	niter := int(niter64)

	var wg sync.WaitGroup
	start := time.Now()
	wg.Add(nproc)
	for g := 0; g < nproc; g++ {
		go func(g int) {
			defer wg.Done()
			err := do_bench_loop(g, "Hello world.", niter, 1, 1)
			if err != nil {
				t.Fatal(err)
			}
		}(g)
	}
	wg.Wait()

	end := time.Now()
	elapsed := end.Sub(start)
	fmt.Printf("%d threads, %d iter, %v elapsed\n", nproc, niter, elapsed)
}
