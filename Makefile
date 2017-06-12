CODE := $(shell find src -name "*.v")
COQRFLAGS := -R build Pocs

.PHONY: default
default: _CoqProject coq extract

build/%.v: src/%.v
	@mkdir -p $(@D)
	@rm -f $@
	@ln -s $(shell pwd)/$< $@
.PRECIOUS: build/%.v

build/%.v.d: build/%.v $(patsubst src/%.v,build/%.v,$(CODE))
	coqdep -c $(COQRFLAGS) $< > $@
.PRECIOUS: build/%.v.d

-include $(patsubst src/%.v,build/%.v.d,$(CODE))

build/%.vo: build/%.v
	coqc -q $(COQRFLAGS) $<
.PRECIOUS: build/%.vo

.PHONY: coq
coq: $(patsubst src/%.v,build/%.vo,$(CODE))

.PHONY: extract
extract: ExtractReplicatedDisk.v coq replicate-nbd/fiximports.py
	coqtop -R src Pocs -noglob < $<
	./scripts/add-preprocess.sh replicate-nbd/src/*.hs

.PHONY: hs
hs: extract
	cd replicate-nbd; stack build

.PHONY: clean
clean:
	rm -rf build
	rm -f replicate-nbd/src/*.hs

_CoqProject: _CoqProject.in
	cat _CoqProject.in > $@
