CODE := $(wildcard src/POCS.v)
CODE += $(wildcard src/Helpers/*.v)
CODE += $(wildcard src/SepLogic/Pred/*.v)
CODE += $(wildcard src/SepLogic/Mem/*.v)
CODE += $(wildcard src/Refinement/*.v)
CODE += $(wildcard src/Disk/*.v)

## For StatDB lab
CODE += $(wildcard src/Variables/*.v)
CODE += $(wildcard src/StatDb/*.v)

## For bad sector remapping lab
CODE += $(wildcard src/BadSectorDisk/*.v)
CODE += $(wildcard src/RemappedDisk/*.v)
CODE += $(wildcard src/NBD/*.v)

## For atomic pair lab
CODE += $(wildcard src/OneDisk/*.v)
CODE += $(wildcard src/AtomicPair/*.v)

## For disk mirroring lab
CODE += $(wildcard src/TwoDisk/*.v)
CODE += $(wildcard src/ReplicatedDisk/*.v)

COQRFLAGS := -R build POCS

BINS	:= statdb-cli remap-nbd replicate-nbd

.PHONY: default
default: $(patsubst %,bin/%,$(BINS)) docs

build/%.v: src/%.v
	@mkdir -p $(@D)
	@rm -f $@
	@ln -s "$(shell pwd)"/$< $@
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

.PHONY: docs
docs: coq
	@mkdir -p doc
	coqdoc $(COQRFLAGS) -d doc $(patsubst src/%.v,build/%.v,$(CODE))

.PHONY: %/extract
%/extract: %/Extract.v %/fiximports.py build/Helpers/ExtrBytes.vo build/Refinement/ExtrProg.vo
	@mkdir -p $@
	coqtop $(COQRFLAGS) -batch -noglob -load-vernac-source $<
	./scripts/add-preprocess.sh $@/*.hs

statdb-cli/extract: build/StatDb/StatDbCli.vo
remap-nbd/extract: build/RemappedDisk/RemappedServer.vo
replicate-nbd/extract: build/ReplicatedDisk/ReplicatedServer.vo

bin/%: %/extract
	mkdir -p $(@D)
	cd $(patsubst %/extract,%,$<) && PATH=$(PATH):"$(shell pwd)"/bin stack build --copy-bins --local-bin-path ../bin

.PHONY: clean
clean:
	rm -rf build
	rm -rf doc
	rm -rf $(foreach d,$(BINS),$(d)/extract)
	rm -rf $(foreach d,$(BINS),$(d)/.stack-work)
	rm -f $(foreach b,$(BINS),bin/$(b))
