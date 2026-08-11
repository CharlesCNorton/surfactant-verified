# Verification

`surfactant.v` is the source of truth. Three independent checks run against it: a
Promela model for SPIN, a timed-automata model for UPPAAL, and the OCaml
extraction cross-validated against a Python reference implementation and against
published trial profiles.

## Artifacts

| File | Role |
|------|------|
| `surfactant.v` | Coq formalization, deductive proofs |
| `surfactant.pml` | Promela model for SPIN |
| `surfactant.xml` | Timed automata model for UPPAAL |
| `run_spin.py` | Promela preprocessor and verification driver |
| `cross_validate.py` | OCaml extraction against Python reference |
| `validate_literature.py` | Extraction against published trial profiles |
| `literature_validation_cases.json` | Trial-derived case definitions |

## Timing Constants

Shared by the Coq, Promela, and UPPAAL models.

| Constant | Value | Meaning |
|----------|-------|---------|
| `SURFACTANT_WINDOW_MAX` | 120 min | Two hours from RDS onset to administration |
| `RESPONSE_EVAL_MIN` | 120 min | Minimum time before response evaluation |
| `RESPONSE_EVAL_MAX` | 360 min | Maximum time for response evaluation |
| `REPEAT_INTERVAL_MIN` | 360 min | Minimum six hours between doses |
| `MAX_DOSES` | 4 | Maximum surfactant doses |

## SPIN

### Prerequisites

SPIN from http://spinroot.com/spin/whatispin.html. A C preprocessor is required
even for syntax checking.

```bash
sudo apt-get install spin     # Debian/Ubuntu
brew install spin             # macOS
```

On Windows, install MinGW-w64 for `gcc` and add it to `PATH`, or use WSL.

### Usage

```bash
spin -a surfactant.pml              # syntax check and generate verifier
gcc -o pan pan.c                    # compile verifier
./pan -a                            # verify all properties
./pan -a -N p_contra_blocks         # verify one property
spin -p surfactant.pml              # print execution trace
spin -t surfactant.pml              # guided simulation after verification
```

`run_spin.py` drives preprocessing and verification, emitting `surfactant_pp.pml`.

### LTL Properties

| Property | Formula | Description |
|----------|---------|-------------|
| `p_contra_blocks` | `[](has_contraindication -> !surfactant_given)` | Contraindication always blocks treatment |
| `p_window_respected` | `[](location==Surfactant_Given -> clock<=120)` | Surfactant given within the two-hour window |
| `p_response_timing` | `[](Responded\|\|NonResponder -> clock>=120)` | Response evaluated within the valid window |
| `p_max_doses` | `[](doses_given <= 4)` | Maximum four doses never exceeded |
| `p_repeat_interval` | `[](Surfactant_Given && doses>1 -> interval>=360)` | Repeat doses respect the six-hour minimum |
| `p_liveness` | `[](indicated && !contra -> <>(given \|\| !window))` | If indicated, eventually treated or window expires |
| `p_well_infant` | `[]((GA>=210 && fio2<=30) -> !indicated)` | Well infant never indicated |
| `p_no_deadlock` | `[]<>(Weaned \|\| Contraindicated \|\| doses>=4)` | System reaches a terminal state |

### Results

SPIN 6.4.9, run 2026-01-04 against `surfactant.pml`.

| Property | Result | States | Errors |
|----------|--------|--------|--------|
| `p_contra_blocks` | PASS | 10 | 0 |
| `p_window_respected` | PASS | 10 | 0 |
| `p_max_doses` | PASS | 10 | 0 |
| `p_well_infant` | PASS | 10 | 0 |
| `p_response_timing` | PASS | 10 | 0 |
| `p_repeat_interval` | PASS | 10 | 0 |
| `p_liveness` | PASS | 10 | 0 |
| `p_no_deadlock` | CYCLE | - | - |

`p_no_deadlock` reports an acceptance cycle in the `Initial` state. With
`env_rds_detected=false` the system remains in `Initial` indefinitely, which is
the intended encoding of a patient who never develops RDS.

### Model Structure

```
TA_Initial
    |
    v (RDS detected)
TA_RDS_Diagnosed
    |
    +---> TA_Contraindicated (if contraindication)
    |
    v
TA_Evaluating
    |
    v (surfactant given within window)
TA_Surfactant_Given
    |
    v
TA_Monitoring
    |
    +---> TA_Responded ---> TA_Weaned
    |
    v (poor response)
TA_NonResponder
    |
    +---> TA_Evaluating (repeat dose if eligible)
```

## UPPAAL

### Prerequisites

UPPAAL from https://uppaal.org/downloads/, free for academic and non-commercial
use.

### Usage

Open `surfactant.xml`, then use the Simulator tab to step through transitions and
the Verifier tab to check queries. Patient parameters are set in the Declarations
tab:

```c
int ga_total_days = 196;    // 28 weeks
int fio2 = 45;              // FiO2 45%
bool intubated = true;
bool has_rds_signs = true;
bool has_contraindication = false;
```

### Locations

| Location | Invariant | Description |
|----------|-----------|-------------|
| `Initial` | - | Pre-diagnosis |
| `RDS_Diagnosed` | `time_since_rds <= 120` | Clock starts |
| `Evaluating` | `time_since_rds <= 120` | Must act within window |
| `Surfactant_Given` | committed | Immediate transition |
| `Monitoring` | `time_since_dose <= 360` | Post-dose observation |
| `Responded` | - | Good response |
| `NonResponder` | - | Consider repeat |
| `Weaned` | - | Terminal, success |
| `Contraindicated` | - | Terminal, blocked |
| `WindowExpired` | - | Terminal, missed window |
| `MaxDoses` | - | Terminal, maximum reached |

### Clocks

| Clock | Purpose |
|-------|---------|
| `time_since_rds` | Minutes since RDS diagnosis |
| `time_since_dose` | Minutes since last surfactant dose |

### Queries

| Query | Property |
|-------|----------|
| `A[] (has_contraindication imply !surfactant_given)` | Contraindication blocks treatment |
| `A[] (surfactant_given imply time_since_rds <= 120)` | Window respected |
| `A[] (doses_given <= MAX_DOSES)` | Maximum doses bounded |
| `A[] (therapy.Responded imply time_since_dose >= 120)` | Response timing valid |
| `A[] ((ga >= 210 && fio2 <= 30) imply !indicated)` | Well infant excluded |
| `E<> therapy.Weaned` | Weaning reachable |
| `E<> therapy.Surfactant_Given` | Treatment reachable |
| `A[] not deadlock` | No deadlock |
| `Evaluating --> (Given \|\| Expired)` | Liveness |

`A[]` is "for all paths, always". `E<>` is "there exists a path where eventually".
`-->` is leads-to.

### State Machine

```
                          +------------------+
                          |  Contraindicated |
                          +------------------+
                                  ^
                                  | has_contraindication
                                  |
+----------+    rds     +--------------+   !contra   +------------+
| Initial  | --------> | RDS_Diagnosed | ----------> | Evaluating |
+----------+            +--------------+             +------------+
                                                        |     |
                              +-------------------------+     |
                              |                               |
                              v                               v
                      +---------------+             +-----------------+
                      | WindowExpired |             | Surfactant_Given|
                      +---------------+             +-----------------+
                                                           |
                                                           v
                      +------------+               +------------+
                      |   Weaned   | <------------ | Monitoring |
                      +------------+    good       +------------+
                                                     |       |
                              +-----------+          |       |
                              |           |   poor   |       |
                              v           +----------+       |
                      +------------+                         |
                      | MaxDoses   | <--- doses >= 4 --------+
                      +------------+                         |
                              ^                              |
                              |                              v
                              |                    +--------------+
                              +------------------- | NonResponder |
                                  doses < 4        +--------------+
                                  wait 6h                |
                                  fio2 > 30             |
                                       +----------------+
                                       | repeat eligible
                                       v
                                 (back to Evaluating)
```

## Correspondence with Coq

| Coq | Promela | UPPAAL |
|-----|---------|--------|
| `TALocation` inductive | `mtype` locations | Locations |
| `Definition` values | `#define` constants | Constants |
| `minutes_since_*` parameters | Clock variables | Clocks |
| `*_ok` predicates | Guards | Invariants |
| `*_threshold` comparisons | Guards | Guards |
| Theorems | `ltl` properties | CTL queries |
| Quantified propositions | Nondeterministic choice | Nondeterministic edges |

Coq supplies deductive proofs. SPIN and UPPAAL supply exhaustive state-space
exploration and counterexample generation.

## Cross-Validation

The OCaml extraction (`surfactant_cli`), a Python reference implementation, and
the SPIN model were run against a shared case set on 2026-01-04. All 12 cases
agreed across all three.

| Case | Input | Expected |
|------|-------|----------|
| TC01 | GA 27+0 (189d), FiO2 45%, 2 signs, no contra, CPAP | Indicated |
| TC02 | GA 34+0 (238d), FiO2 21%, 0 signs, no contra | NotIndicated |
| TC03 | GA 27+0 (189d), FiO2 50%, 3 signs, CDH | NotIndicated |
| TC04 | GA 26+0 (182d), FiO2 40%, 0 signs, intubated, 5 min | Indicated |
| TC05 | GA 29+6 (209d), FiO2 30%, intubated, 5 min | Indicated |
| TC06 | GA 30+0 (210d), FiO2 25%, intubated, 5 min | NotIndicated |
| TC07 | GA 32+0 (224d), FiO2 30%, 2 signs, CPAP | NotIndicated |
| TC08 | GA 32+0 (224d), FiO2 31%, 2 signs, CPAP | Indicated |
| TC09 | GA 32+0 (224d), FiO2 50%, 1 sign, CPAP | NotIndicated |
| TC10 | GA 28+0, weight 1000 g, Survanta | Indicated, 100 mg |
| TC11 | GA 27+0, weight 900 g, Curosurf | Indicated, 180 mg |
| TC12 | GA 26+0, FiO2 60%, 4 signs, lethal anomaly + pneumothorax | NotIndicated |

### Boundaries Exercised

- Gestational age: 209 days indicated, 210 days not indicated
- FiO2: 30% not indicated, 31% indicated
- Sign count: one sign not indicated, two signs indicated
- Contraindication: any true yields NotIndicated regardless of other criteria

### Dose Calculation

Rounding is `(weight * dose_per_kg + 500) / 1000`.

- Survanta at 100 mg/kg: 1000 g yields 100 mg
- Curosurf at 200 mg/kg: 900 g yields 180 mg

## Literature Validation

`validate_literature.py` runs the extraction against trial-derived profiles in
`literature_validation_cases.json` and writes `VALIDATION_RESULTS.json`. The
2026-01-04 run covered 15 cases with 15 concordant, 0 discordant, 0 errors.
Cases include the SUPPORT trial prophylactic profile at 26 weeks intubated at
five minutes, and the prophylactic eligibility boundary at 29+6 and 30+0 weeks.
