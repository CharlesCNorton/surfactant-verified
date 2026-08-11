# surfactant-verified

A Rocq formalization of surfactant administration criteria for neonatal
respiratory distress syndrome, with OCaml extraction and independent model
checking.

`surfactant.v` is the source of truth. It defines the indication logic
(prophylactic and rescue), contraindications, dosing by preparation and weight,
the timed treatment automaton, and the repeat-dose constraints, together with the
proofs that those rules are consistent.

## Layout

| File | Contents |
|------|----------|
| `surfactant.v` | Formalization and proofs, extraction directive |
| `surfactant.pml` | Promela model for SPIN |
| `surfactant.xml` | Timed automata model for UPPAAL |
| `surfactant_cli.ml` | Command-line decision interface |
| `test_surfactant.ml` | Unit tests against the extraction |
| `fuzz_surfactant.ml` | Randomized property tests |
| `cross_validate.py` | Extraction against a Python reference implementation |
| `validate_literature.py` | Extraction against published trial profiles |
| `literature_validation_cases.json` | Trial-derived case definitions |
| `run_spin.py` | Promela preprocessor and verification driver |
| `server.py`, `test_server.py` | HTTP decision service and its tests |
| `VERIFICATION.md` | SPIN and UPPAAL models, properties, and results |

`surfactant_decision.ml` and `surfactant_decision.mli` are extraction output and
are not tracked. `make` regenerates them from `surfactant.v`.

## Build

```bash
make coq      # compile surfactant.v and extract the OCaml decision module
make ocaml    # build the CLI, unit tests, and fuzzer
make test     # run the unit tests
make fuzz     # run the randomized property tests
```

Requires Rocq 9.0 or later and an OCaml toolchain. `make` alone builds both
halves.

## Model Checking

See `VERIFICATION.md` for the SPIN and UPPAAL models, the properties checked
against each, and the recorded results.

## Scope

The criteria encoded here follow published guidance for surfactant replacement in
neonatal RDS. This is a formalization of that guidance, not a clinical decision
device, and it has not been validated against a NICU cohort.

## License

MIT. See `LICENSE`.
