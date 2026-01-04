# SPIN Model Checking for Surfactant Decision Logic

This directory contains a Promela model (`surfactant.pml`) for formal verification
of the surfactant therapy state machine using the SPIN model checker.

## Files

- `surfactant.pml` - Promela model translated from `surfactant.v`
- `surfactant.v` - Original Coq formalization (source of truth)

## Prerequisites

### SPIN
Install SPIN: http://spinroot.com/spin/whatispin.html

```bash
# Ubuntu/Debian
sudo apt-get install spin

# macOS (Homebrew)
brew install spin

# Windows (requires gcc for preprocessing)
# 1. Install MinGW-w64: https://www.mingw-w64.org/downloads/
# 2. Add to PATH: C:\mingw64\bin
# 3. Download SPIN binary from Spin repo Bin/ folder
```

### GCC Requirement
SPIN requires a C preprocessor (gcc) even for syntax checking.
On Windows, install MinGW-w64 or use WSL.

### Included Files
- `spin649.exe` - SPIN 6.4.9 binary (Windows x64)
- `run_spin.py` - Preprocessor and verification script
- `surfactant_pp.pml` - Preprocessed model (generated)

## Usage

### 1. Syntax Check
```bash
spin -a surfactant.pml
```

### 2. Compile Verifier
```bash
gcc -o pan pan.c
```

### 3. Verify All Properties
```bash
./pan -a
```

### 4. Verify Specific Property
```bash
./pan -a -N p_contra_blocks    # Contraindication blocks treatment
./pan -a -N p_window_respected # Surfactant window respected
./pan -a -N p_max_doses        # Max doses never exceeded
./pan -a -N p_well_infant      # Well infant never indicated
```

### 5. Simulation (Interactive)
```bash
spin -p surfactant.pml         # Print execution trace
spin -t surfactant.pml         # Guided simulation after verification
```

## LTL Properties Verified

| Property | Description |
|----------|-------------|
| `p_contra_blocks` | Contraindication always blocks treatment |
| `p_window_respected` | Surfactant given within 2-hour window |
| `p_response_timing` | Response evaluated within valid window (2-6h) |
| `p_max_doses` | Maximum 4 doses never exceeded |
| `p_repeat_interval` | Repeat doses respect 6-hour minimum |
| `p_liveness` | If indicated, eventually treated or window expires |
| `p_well_infant` | Well infant (GA >= 30w, FiO2 <= 30) never indicated |
| `p_no_deadlock` | System eventually reaches terminal state |

## Model Structure

The model implements the timed automata from `surfactant.v`:

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

## Timing Constants

| Constant | Value | Description |
|----------|-------|-------------|
| `SURFACTANT_WINDOW_MAX` | 120 min | 2 hours from RDS onset |
| `RESPONSE_EVAL_MIN` | 120 min | Minimum time before response eval |
| `RESPONSE_EVAL_MAX` | 360 min | Maximum time for response eval |
| `REPEAT_INTERVAL_MIN` | 360 min | Minimum 6 hours between doses |
| `MAX_DOSES` | 4 | Maximum surfactant doses |

## Correspondence with Coq

| Promela | Coq |
|---------|-----|
| `mtype` locations | `TALocation` inductive |
| `#define` constants | `Definition` values |
| `ltl` properties | Theorems (proven in Coq) |
| Nondeterministic choice | Quantified propositions |

The Coq formalization provides proofs; SPIN provides exhaustive state exploration
and counterexample generation for debugging.
