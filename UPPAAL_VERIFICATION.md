# UPPAAL Timed Automata Verification

This directory contains an UPPAAL model (`surfactant.xml`) for formal verification
of the surfactant therapy state machine with real-time constraints.

## Files

- `surfactant.xml` - UPPAAL timed automata model
- `surfactant.v` - Original Coq formalization (source of truth)

## Prerequisites

Download UPPAAL: https://uppaal.org/downloads/

UPPAAL is free for academic/non-commercial use.

## Usage

### 1. Open Model
```
File -> Open -> surfactant.xml
```

### 2. Edit Parameters (Optional)
In the Declarations tab, modify patient parameters:
```c
int ga_total_days = 196;    // 28 weeks
int fio2 = 45;              // FiO2 45%
bool intubated = true;
bool has_rds_signs = true;
bool has_contraindication = false;
```

### 3. Simulate
- Go to Simulator tab
- Click "Reset" then step through transitions
- Observe clock values and state changes

### 4. Verify
- Go to Verifier tab
- Select queries to verify
- Click "Check"
- Green = satisfied, Red = violated (with counterexample)

## Model Structure

### Locations (States)

| Location | Invariant | Description |
|----------|-----------|-------------|
| `Initial` | - | Pre-diagnosis |
| `RDS_Diagnosed` | `time_since_rds <= 120` | Clock starts |
| `Evaluating` | `time_since_rds <= 120` | Must act within window |
| `Surfactant_Given` | committed | Immediate transition |
| `Monitoring` | `time_since_dose <= 360` | Post-dose observation |
| `Responded` | - | Good response |
| `NonResponder` | - | Consider repeat |
| `Weaned` | - | Terminal: success |
| `Contraindicated` | - | Terminal: blocked |
| `WindowExpired` | - | Terminal: missed window |
| `MaxDoses` | - | Terminal: max reached |

### Clocks

| Clock | Purpose |
|-------|---------|
| `time_since_rds` | Minutes since RDS diagnosis |
| `time_since_dose` | Minutes since last surfactant dose |

### Timing Constants

| Constant | Value | Meaning |
|----------|-------|---------|
| `SURFACTANT_WINDOW_MAX` | 120 | 2 hours to give surfactant |
| `RESPONSE_EVAL_MIN` | 120 | Minimum 2h before response eval |
| `RESPONSE_EVAL_MAX` | 360 | Maximum 6h for response eval |
| `REPEAT_INTERVAL_MIN` | 360 | Minimum 6h between doses |
| `MAX_DOSES` | 4 | Maximum surfactant doses |

## Verification Queries

| Query | Property |
|-------|----------|
| `A[] (has_contraindication imply !surfactant_given)` | Contraindication blocks treatment |
| `A[] (surfactant_given imply time_since_rds <= 120)` | Window respected |
| `A[] (doses_given <= MAX_DOSES)` | Max doses bounded |
| `A[] (therapy.Responded imply time_since_dose >= 120)` | Response timing valid |
| `A[] ((ga >= 210 && fio2 <= 30) imply !indicated)` | Well infant excluded |
| `E<> therapy.Weaned` | Weaning reachable |
| `E<> therapy.Surfactant_Given` | Treatment reachable |
| `A[] not deadlock` | No deadlock |
| `Evaluating --> (Given || Expired)` | Liveness |

### Query Syntax

- `A[]` - For all paths, always (invariant)
- `E<>` - There exists a path where eventually (reachability)
- `-->` - Leads-to (liveness)
- `imply` - Logical implication

## State Machine Diagram

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

| UPPAAL | Coq |
|--------|-----|
| Locations | `TALocation` inductive type |
| Clocks | `minutes_since_*` parameters |
| Invariants | `*_ok` predicates |
| Guards | `*_threshold` comparisons |
| CTL queries | Theorems (proven) |

The Coq formalization provides deductive proofs; UPPAAL provides
exhaustive timed state-space exploration with counterexample generation.
