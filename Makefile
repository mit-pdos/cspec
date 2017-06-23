CODE := $(wildcard src/*.v)
CODE += $(wildcard src/SepLogic/*.v)
CODE += $(wildcard src/SepLogic/Pred/*.v)
CODE += $(wildcard src/SepLogic/Mem/*.v)
CODE += $(wildcard src/Refinement/*.v)
CODE += $(wildcard src/Refinement/ProgLang/*.v)
CODE += $(wildcard src/Disk/*.v)

## For StatDB lab
CODE += $(wildcard src/Variables/*.v)
CODE += $(wildcard src/StatDb/*.v)

## For bad sector remapping lab
CODE += $(wildcard src/BadSectorDisk/*.v)
CODE += $(wildcard src/RemappedDisk/*.v)
CODE += $(wildcard src/NBD/*.v)

## For disk mirroring lab
CODE += $(wildcard src/TwoDisk/*.v)
CODE += $(wildcard src/SeqDisk/ReplicatedDisk/*.v)
CODE += $(wildcard src/SeqDisk/AsyncReplicatedDisk/*.v)
CODE += $(wildcard src/SeqDisk/*.v)

COQRFLAGS := -R build Pocs

.PHONY: default
default: _CoqProject coq extract hs

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
extract: replicate-nbd/ExtractReplicatedDisk.v coq replicate-nbd/fiximports.py
	coqtop $(COQRFLAGS) -batch -noglob -load-vernac-source $<
	./scripts/add-preprocess.sh replicate-nbd/src/*.hs

.PHONY: hs
hs: extract
	cd replicate-nbd && stack build

.PHONY: clean
clean:
	rm -rf build
	rm -f replicate-nbd/src/*.hs

_CoqProject: _CoqProject.in
	cat _CoqProject.in > $@
