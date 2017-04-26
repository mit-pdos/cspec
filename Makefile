.PHONY: coq clean

CODE := $(wildcard *.v)

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(CODE)
	coq_makefile -f _CoqProject > Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
