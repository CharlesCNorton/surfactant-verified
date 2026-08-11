#!/usr/bin/env python3
"""Validation drivers for the extracted surfactant decision logic.

Two case sources:
  cross       Hand-built boundary cases, compared against a Python reference
              implementation of the same rules.
  literature  Cases derived from published thresholds, loaded from
              literature_validation_cases.json.

The decision binary is located via SURFACTANT_CLI, or as surfactant_cli next to
this script. Build it with `make ocaml`.
"""

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CASES_PATH = os.path.join(SCRIPT_DIR, "literature_validation_cases.json")
RESULTS_PATH = os.path.join(SCRIPT_DIR, "VALIDATION_RESULTS.json")

GA_PROPHYLACTIC_MAX_DAYS = 210
FIO2_RESCUE_THRESHOLD = 30
RESCUE_SIGNS_REQUIRED = 2

CLI_DEFAULTS = {
    "cxr": {"ground_glass": False, "air_bronchograms": False,
            "low_volumes": False, "reticulogranular": False},
    "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
    "cpap_trial": {"pressure": 0, "duration": 0, "fio2": 21},
    "product": "curosurf",
}

CROSS_CASES = [
    {"id": "TC01", "name": "Preterm with RDS", "expected": "Indicated",
     "inputs": {"patient": {"ga_weeks": 27, "ga_days": 0, "weight": 900, "age_hours": 6, "fio2": 45},
                "signs": {"grunting": True, "retractions": True},
                "contraindications": {}, "minutes_since_birth": 360,
                "cxr": {"ground_glass": True, "air_bronchograms": True, "low_volumes": True},
                "cpap_trial": {"pressure": 7, "duration": 30, "fio2": 50},
                "support": "cpap", "product": "curosurf"}},
    {"id": "TC02", "name": "Well infant", "expected": "NotIndicated",
     "inputs": {"patient": {"ga_weeks": 34, "ga_days": 0, "weight": 2200, "age_hours": 12, "fio2": 21},
                "signs": {}, "contraindications": {}, "minutes_since_birth": 720,
                "support": "room_air", "product": "survanta"}},
    {"id": "TC03", "name": "Contraindication (CDH) blocks", "expected": "NotIndicated",
     "inputs": {"patient": {"ga_weeks": 27, "ga_days": 0, "weight": 900, "age_hours": 6, "fio2": 50},
                "signs": {"grunting": True, "retractions": True, "nasal_flaring": True},
                "contraindications": {"cdh": True}, "minutes_since_birth": 360,
                "cxr": {"ground_glass": True},
                "cpap_trial": {"pressure": 7, "duration": 30, "fio2": 55},
                "support": "cpap", "product": "curosurf"}},
    {"id": "TC04", "name": "Prophylactic, 26w intubated", "expected": "Indicated",
     "inputs": {"patient": {"ga_weeks": 26, "ga_days": 0, "weight": 750, "age_hours": 0, "fio2": 40},
                "signs": {}, "contraindications": {}, "minutes_since_birth": 5,
                "support": "intubated", "product": "curosurf"}},
    {"id": "TC05", "name": "GA boundary 29+6 (209d)", "expected": "Indicated",
     "inputs": {"patient": {"ga_weeks": 29, "ga_days": 6, "weight": 1350, "age_hours": 0, "fio2": 30},
                "signs": {}, "contraindications": {}, "minutes_since_birth": 5,
                "support": "intubated", "product": "survanta"}},
    {"id": "TC06", "name": "GA boundary 30+0 (210d)", "expected": "NotIndicated",
     "inputs": {"patient": {"ga_weeks": 30, "ga_days": 0, "weight": 1400, "age_hours": 0, "fio2": 25},
                "signs": {}, "contraindications": {}, "minutes_since_birth": 5,
                "support": "intubated", "product": "survanta"}},
    {"id": "TC07", "name": "FiO2 boundary 30%", "expected": "NotIndicated",
     "inputs": {"patient": {"ga_weeks": 32, "ga_days": 0, "weight": 1800, "age_hours": 6, "fio2": 30},
                "signs": {"grunting": True, "retractions": True},
                "contraindications": {}, "minutes_since_birth": 360,
                "blood_gas": {"ph": 7320, "pco2": 45, "po2": 70},
                "support": "cpap", "product": "curosurf"}},
    {"id": "TC08", "name": "FiO2 boundary 31%", "expected": "Indicated",
     "inputs": {"patient": {"ga_weeks": 32, "ga_days": 0, "weight": 1800, "age_hours": 6, "fio2": 31},
                "signs": {"grunting": True, "retractions": True},
                "contraindications": {}, "minutes_since_birth": 360,
                "cxr": {"ground_glass": True},
                "blood_gas": {"ph": 7320, "pco2": 45, "po2": 70},
                "cpap_trial": {"pressure": 6, "duration": 30, "fio2": 35},
                "support": "cpap", "product": "curosurf"}},
    {"id": "TC09", "name": "Single sign insufficient", "expected": "NotIndicated",
     "inputs": {"patient": {"ga_weeks": 32, "ga_days": 0, "weight": 1800, "age_hours": 6, "fio2": 50},
                "signs": {"grunting": True}, "contraindications": {},
                "minutes_since_birth": 360, "support": "cpap", "product": "curosurf"}},
    {"id": "TC10", "name": "Dose, Survanta 1000g", "expected": "Indicated", "dose_mg": 100,
     "inputs": {"patient": {"ga_weeks": 28, "ga_days": 0, "weight": 1000, "age_hours": 0, "fio2": 40},
                "signs": {}, "contraindications": {}, "minutes_since_birth": 5,
                "support": "intubated", "product": "survanta"}},
    {"id": "TC11", "name": "Dose, Curosurf 900g", "expected": "Indicated", "dose_mg": 180,
     "inputs": {"patient": {"ga_weeks": 27, "ga_days": 0, "weight": 900, "age_hours": 0, "fio2": 40},
                "signs": {}, "contraindications": {}, "minutes_since_birth": 5,
                "support": "intubated", "product": "curosurf"}},
    {"id": "TC12", "name": "Multiple contraindications", "expected": "NotIndicated",
     "inputs": {"patient": {"ga_weeks": 26, "ga_days": 0, "weight": 700, "age_hours": 1, "fio2": 60},
                "signs": {"grunting": True, "retractions": True, "nasal_flaring": True, "cyanosis": True},
                "contraindications": {"lethal_anomaly": True, "pneumothorax": True},
                "minutes_since_birth": 60,
                "blood_gas": {"ph": 7200, "pco2": 70, "po2": 40},
                "support": "intubated", "product": "curosurf"}},
]


def find_cli():
    """Locate the decision binary."""
    env = os.environ.get("SURFACTANT_CLI")
    if env:
        return env
    for name in ("surfactant_cli", "surfactant_cli.exe"):
        path = os.path.join(SCRIPT_DIR, name)
        if os.path.exists(path):
            return path
    return None


def run_cli(cli, inputs):
    """Send one case to the decision binary and return its parsed response."""
    request = dict(CLI_DEFAULTS)
    request.update(inputs)
    try:
        proc = subprocess.run([cli], input=json.dumps(request),
                              capture_output=True, text=True, timeout=10)
    except subprocess.TimeoutExpired:
        return {"result": "Error", "error": "timeout"}
    except OSError as exc:
        return {"result": "Error", "error": str(exc)}
    if proc.returncode != 0:
        return {"result": "Error", "error": proc.stderr.strip()}
    try:
        return json.loads(proc.stdout.strip())
    except json.JSONDecodeError as exc:
        return {"result": "Error", "error": "unparsable output: %s" % exc}


def reference_decision(inputs):
    """Python reference implementation of the indication rules."""
    patient = inputs["patient"]
    signs = inputs.get("signs", {})
    contras = inputs.get("contraindications", {})

    ga_days = patient["ga_weeks"] * 7 + patient["ga_days"]
    sign_count = sum(bool(signs.get(k)) for k in
                     ("grunting", "retractions", "nasal_flaring", "cyanosis"))
    has_contra = any(bool(contras.get(k)) for k in
                     ("cdh", "lethal_anomaly", "pulmonary_hypoplasia",
                      "pulmonary_hemorrhage", "pneumothorax"))

    prophylactic = ga_days < GA_PROPHYLACTIC_MAX_DAYS
    rescue = (patient["fio2"] > FIO2_RESCUE_THRESHOLD
              and sign_count >= RESCUE_SIGNS_REQUIRED)
    indicated = not has_contra and (prophylactic or rescue)

    return {"ga_days": ga_days, "sign_count": sign_count,
            "has_contra": has_contra, "prophylactic": prophylactic,
            "rescue": rescue,
            "result": "Indicated" if indicated else "NotIndicated"}


def report(title, rows, total):
    """Print a per-case table and a summary, returning the failure count."""
    print("=" * 70)
    print(title)
    print("=" * 70)
    failures = 0
    for row in rows:
        mark = {"PASS": "[OK]", "FAIL": "[XX]", "ERROR": "[??]"}[row["status"]]
        print("%s %-6s %s" % (mark, row["id"], row["description"][:52]))
        if row["status"] != "PASS":
            failures += 1
            print("        expected %s, got %s" % (row["expected"], row["actual"]))
            if row.get("error"):
                print("        %s" % row["error"][:60])
    print("-" * 70)
    print("total %d, passed %d, failed %d" % (total, total - failures, failures))
    return failures


def run_cross(cli):
    """Compare the extraction against the Python reference on boundary cases."""
    rows = []
    for case in CROSS_CASES:
        expected = case["expected"]
        response = run_cli(cli, case["inputs"])
        actual = response.get("result", "Error")
        ref = reference_decision(case["inputs"])

        if actual == "Error":
            status = "ERROR"
        elif actual == expected and ref["result"] == expected:
            status = "PASS"
        else:
            status = "FAIL"

        if status == "PASS" and "dose_mg" in case:
            if response.get("dose_mg") != case["dose_mg"]:
                status = "FAIL"
                actual = "%s dose=%s" % (actual, response.get("dose_mg"))

        rows.append({"id": case["id"], "description": case["name"],
                     "expected": expected, "actual": actual,
                     "reference": ref["result"], "status": status,
                     "error": response.get("error")})
    return rows, report("CROSS-VALIDATION (extraction vs reference)", rows, len(CROSS_CASES))


def run_literature(cli):
    """Compare the extraction against cases derived from published thresholds."""
    with open(CASES_PATH) as handle:
        data = json.load(handle)
    cases = data["cases"]

    print("sources:")
    for src in data["metadata"]["sources"]:
        print("  %s" % src)
    print()

    rows = []
    for case in cases:
        expected = case["expected"]
        inputs = {k: case[k] for k in
                  ("patient", "signs", "contraindications",
                   "minutes_since_birth", "support") if k in case}
        for optional in ("cxr", "blood_gas", "cpap_trial", "product",
                         "clinical_judgement"):
            if optional in case:
                inputs[optional] = case[optional]

        response = run_cli(cli, inputs)
        actual = response.get("result", "Error")
        status = "ERROR" if actual == "Error" else ("PASS" if actual == expected else "FAIL")
        rows.append({"id": case["id"], "description": case["description"],
                     "expected": expected, "actual": actual, "status": status,
                     "error": response.get("error")})

    failures = report("LITERATURE VALIDATION", rows, len(cases))
    payload = {
        "run_date": datetime.now().isoformat(),
        "summary": {"total": len(cases), "concordant": len(cases) - failures,
                    "discordant": failures,
                    "agreement_rate": (len(cases) - failures) / len(cases) if cases else 0},
        "results": rows,
    }
    with open(RESULTS_PATH, "w") as handle:
        json.dump(payload, handle, indent=2)
    print("results written to %s" % RESULTS_PATH)
    return rows, failures


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", nargs="?", default="all",
                        choices=["cross", "literature", "all"],
                        help="which case source to run (default: all)")
    args = parser.parse_args()

    cli = find_cli()
    if cli is None:
        print("decision binary not found; set SURFACTANT_CLI or run `make ocaml`",
              file=sys.stderr)
        return 1

    failures = 0
    if args.mode in ("cross", "all"):
        _, failed = run_cross(cli)
        failures += failed
    if args.mode == "all":
        print()
    if args.mode in ("literature", "all"):
        _, failed = run_literature(cli)
        failures += failed
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
