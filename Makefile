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

## For disk mirroring lab
CODE += $(wildcard src/TwoDisk/*.v)
CODE += $(wildcard src/ReplicatedDisk/*.v)

COQRFLAGS := -R build Pocs

BINS	:= statdb-cli remap-nbd replicate-nbd

.PHONY: default
default: $(patsubst %,bin/%,$(BINS))

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

.PHONY: %/extract
%/extract: %/Extract.v %/fiximports.py build/Helpers/ExtrBytes.vo build/Refinement/ExtrProg.vo
	coqtop $(COQRFLAGS) -batch -noglob -load-vernac-source $<
	./scripts/add-preprocess.sh $(patsubst %/extract,%/src/*.hs,$@)

statdb-cli/extract: build/StatDb/StatDbCli.vo
remap-nbd/extract: build/RemappedDisk/Server.vo
replicate-nbd/extract: build/ReplicatedDisk/Server.vo

bin/%: %/extract
	mkdir -p $(@D)
	cd $(patsubst %/extract,%,$<) && PATH=$(PATH):$(shell pwd)/bin stack build --copy-bins --local-bin-path ../bin

.PHONY: clean
clean:
	rm -rf build
	rm -f $(foreach d,$(BINS),$(d)/src/*.hs)
	rm -rf $(foreach d,$(BINS),$(d)/.stack-work)
	rm -f $(foreach b,$(BINS),bin/$(b))
