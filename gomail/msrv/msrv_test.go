package main

import (
	"fmt"
	"math/rand"
	"strconv"
	"sync"
	"testing"
	"time"
)

const (
	N     = 1
	NUSER = 100
)

func do_bench_loop(tid int, msg string, niter int, nsmtpiter int, npopiter int) error {
	r := rand.New(rand.NewSource(time.Now().UnixNano()))
	for l := 0; l < niter; l++ {
		for i := 0; i < nsmtpiter; i++ {
			u := "u" + strconv.Itoa(r.Int()%NUSER)
			if validUser(u) {
				m := &Message{To: u, Data: []string{msg}}
				m.process_msg(tid)
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
					mbox.retr(&f)
					mbox.dele(&f)
				}
			} else {
				return fmt.Errorf("Invalid user %v", u)
			}
		}
	}
	return nil
}

func TestMixedLoad(t *testing.T) {
	var wg sync.WaitGroup
	start := time.Now()
	wg.Add(N)
	for g := 0; g < N; g++ {
		go func() {
			defer wg.Done()
			err := do_bench_loop(g, "msg", 100000/N, 1, 1)
			if err != nil {
				t.Fatal(err)
			}
		}()
	}
	wg.Wait()
	end := time.Now()
	elapsed := end.Sub(start)
	fmt.Printf("time %v\n", elapsed)
}
