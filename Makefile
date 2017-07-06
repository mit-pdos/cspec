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

## For replicated disk lab
CODE += $(wildcard src/ReplicatedDisk/*.v)

## For disk mirroring lab
CODE += $(wildcard src/TwoDisk/*.v)
CODE += $(wildcard src/SeqDisk/ReplicatedDisk/*.v)
CODE += $(wildcard src/SeqDisk/AsyncReplicatedDisk/*.v)
CODE += $(wildcard src/SeqDisk/*.v)

COQRFLAGS := -R build Pocs

BINS	:= statdb-cli replicate-nbd

.PHONY: default
default: _CoqProject $(patsubst %,bin/%,$(BINS))

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

.PHONY: %/extract
%/extract: %/Extract.v %/fiximports.py build/ExtrBytes.vo build/Refinement/ProgLang/ExtrProg.vo
	coqtop $(COQRFLAGS) -batch -noglob -load-vernac-source $<
	./scripts/add-preprocess.sh $(patsubst %/extract,%/src/*.hs,$@)

replicate-nbd/extract: build/NBD/ExtrServer.vo
statdb-cli/extract: build/StatDb/StatDbCli.vo

bin/%: %/extract
	mkdir -p $(@D)
	cd $(patsubst %/extract,%,$<) && PATH=$(PATH):$(shell pwd)/bin stack build --copy-bins --local-bin-path ../bin

.PHONY: clean
clean:
	rm -rf build
	rm -f $(foreach d,$(BINS),$(d)/src/*.hs)
	rm -rf $(foreach d,$(BINS),$(d)/.stack-work)
	rm -f $(foreach b,$(BINS),bin/$(b))

_CoqProject: _CoqProject.in
	cat _CoqProject.in > $@
