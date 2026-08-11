ROCQ ?= rocq
OCAMLOPT ?= ocamlfind ocamlopt

EXTRACTED := surfactant_decision.ml surfactant_decision.mli
PROGRAMS  := surfactant_cli test_surfactant fuzz_surfactant

.PHONY: all coq ocaml test fuzz validate spin clean

all: coq ocaml

coq: surfactant.vo

surfactant.vo $(EXTRACTED): surfactant.v
	$(ROCQ) compile surfactant.v

ocaml: $(PROGRAMS)

surfactant_cli: $(EXTRACTED) surfactant_cli.ml
	$(OCAMLOPT) -o $@ surfactant_decision.mli surfactant_decision.ml surfactant_cli.ml

test_surfactant: $(EXTRACTED) test_surfactant.ml
	$(OCAMLOPT) -o $@ surfactant_decision.mli surfactant_decision.ml test_surfactant.ml

fuzz_surfactant: $(EXTRACTED) fuzz_surfactant.ml
	$(OCAMLOPT) -o $@ surfactant_decision.mli surfactant_decision.ml fuzz_surfactant.ml

test: test_surfactant
	./test_surfactant

fuzz: fuzz_surfactant
	./fuzz_surfactant

validate: surfactant_cli
	SURFACTANT_CLI=./surfactant_cli python validate.py all

spin:
	python run_spin.py

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux .lia.cache
	rm -f $(EXTRACTED) surfactant_pp.pml
	rm -f *.cmi *.cmx *.o $(PROGRAMS) $(addsuffix .exe,$(PROGRAMS))
	rm -f pan pan.c pan.[bhmpt]
