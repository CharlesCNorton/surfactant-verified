ROCQ ?= rocq
OCAMLOPT ?= ocamlfind ocamlopt

COQ_SRC   := coq/surfactant.v
EXTRACTED := ocaml/surfactant_decision.ml ocaml/surfactant_decision.mli
PROGRAMS  := surfactant_cli test_surfactant fuzz_surfactant
BINARIES  := $(addprefix bin/,$(PROGRAMS))

.PHONY: all coq ocaml test fuzz validate spin serve clean

all: coq ocaml

coq: coq/surfactant.vo

coq/surfactant.vo $(EXTRACTED): $(COQ_SRC)
	$(ROCQ) compile -output-directory ocaml $(COQ_SRC)

ocaml: $(BINARIES)

bin:
	mkdir -p bin

bin/%: $(EXTRACTED) ocaml/%.ml | bin
	$(OCAMLOPT) -I ocaml -o $@ \
	  ocaml/surfactant_decision.mli ocaml/surfactant_decision.ml ocaml/$*.ml

test: bin/test_surfactant
	./bin/test_surfactant

fuzz: bin/fuzz_surfactant
	./bin/fuzz_surfactant

validate: bin/surfactant_cli
	python tools/validate.py all

spin:
	python tools/validate.py spin

serve: bin/surfactant_cli
	python tools/server.py

clean:
	rm -f coq/*.vo coq/*.vok coq/*.vos coq/*.glob coq/.*.aux coq/.lia.cache
	rm -f $(EXTRACTED) models/surfactant_pp.pml VALIDATION_RESULTS.json
	rm -f ocaml/*.cmi ocaml/*.cmx ocaml/*.o
	rm -rf bin
	rm -f pan pan.c pan.[bhmpt]
