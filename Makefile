.PHONY: coq clean

CODE := $(shell git ls-files "*.v")

all: _CoqProject coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(CODE) _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq _CoqProject

_CoqProject: $(CODE) _CoqProject.in
	{ cat _CoqProject.in; git ls-files "*.v"; } > $@
