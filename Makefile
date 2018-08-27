## Common library code
CODE += $(wildcard src/Helpers/*.v)
CODE += $(wildcard src/Helpers/*/*.v)
CODE += $(wildcard src/Spec/*.v)
CODE += $(wildcard src/Spec/*/*.v)
CODE += $(wildcard src/*.v)

COQRFLAGS := -R build CSPEC

.PHONY: default
default: build/CSPEC.vo docs bin/mclnt bin/gomail

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
	coqdoc $(COQRFLAGS) -g --interpolate -d doc $(patsubst src/%.v,build/%.v,$(CODE))

bin/mclnt: gomail/mclnt/mclnt.go
	go build -o bin/mclnt $<
bin/gomail: gomail/msrv/msrv.go
	go build -o bin/gomail $<

.PHONY: clean
clean:
	rm -rf build
	rm -rf doc
