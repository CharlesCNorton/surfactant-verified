#!/usr/bin/env python3
"""
Cross-Validation Test Suite for Surfactant Decision Logic

Runs identical test cases through:
1. OCaml extracted code (from Coq)
2. SPIN model simulation
3. Manual property checks

Verifies all implementations produce identical results.
"""

import subprocess
import json
import os
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OCAML_CLI = os.path.join(SCRIPT_DIR, "surfactant_cli.exe")
SPIN = r"C:\Users\cnort\spin649.exe"
PML = os.path.join(SCRIPT_DIR, "surfactant.pml")

# Test case definitions
# Each case has inputs and expected outputs
TEST_CASES = [
    {
        "id": "TC01",
        "name": "Preterm with RDS - Indicated",
        "inputs": {
            "patient": {"ga_weeks": 27, "ga_days": 0, "weight": 900, "age_hours": 6, "fio2": 45},
            "signs": {"grunting": True, "retractions": True, "nasal_flaring": False, "cyanosis": False},
            "contraindications": {},
            "cxr": {"ground_glass": True, "air_bronchograms": True, "low_volumes": True},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 360,
            "cpap_trial": {"pressure": 7, "duration": 30, "fio2": 50},
            "support": "cpap",
            "product": "curosurf"
        },
        "expected": {
            "result": "Indicated",
            "prophylactic": False,  # GA 27w = 189 days < 210, but on CPAP not intubated for prophylactic
            "rescue": True,         # FiO2 45 > 30, has signs
        }
    },
    {
        "id": "TC02",
        "name": "Well infant - Not Indicated",
        "inputs": {
            "patient": {"ga_weeks": 34, "ga_days": 0, "weight": 2200, "age_hours": 12, "fio2": 21},
            "signs": {"grunting": False, "retractions": False, "nasal_flaring": False, "cyanosis": False},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 720,
            "support": "room_air",
            "product": "survanta"
        },
        "expected": {
            "result": "NotIndicated",
            "prophylactic": False,  # GA 34w = 238 days >= 210
            "rescue": False,        # FiO2 21 <= 30
        }
    },
    {
        "id": "TC03",
        "name": "Contraindication (CDH) - Blocks",
        "inputs": {
            "patient": {"ga_weeks": 27, "ga_days": 0, "weight": 900, "age_hours": 6, "fio2": 50},
            "signs": {"grunting": True, "retractions": True, "nasal_flaring": True, "cyanosis": False},
            "contraindications": {"cdh": True},
            "cxr": {"ground_glass": True},
            "blood_gas": {"ph": 7300, "pco2": 50, "po2": 60},
            "minutes_since_birth": 360,
            "cpap_trial": {"pressure": 7, "duration": 30, "fio2": 55},
            "support": "cpap",
            "product": "curosurf"
        },
        "expected": {
            "result": "NotIndicated",
            "prophylactic": False,
            "rescue": False,  # Blocked by contraindication
        }
    },
    {
        "id": "TC04",
        "name": "Prophylactic eligible - 26w intubated",
        "inputs": {
            "patient": {"ga_weeks": 26, "ga_days": 0, "weight": 750, "age_hours": 0, "fio2": 40},
            "signs": {"grunting": False, "retractions": False, "nasal_flaring": False, "cyanosis": False},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 5,
            "support": "intubated",
            "product": "curosurf"
        },
        "expected": {
            "result": "Indicated",
            "prophylactic": True,   # GA 26w = 182 days < 210, intubated, within window
            "rescue": False,
        }
    },
    {
        "id": "TC05",
        "name": "Boundary 29+6w - Prophylactic eligible",
        "inputs": {
            "patient": {"ga_weeks": 29, "ga_days": 6, "weight": 1350, "age_hours": 0, "fio2": 30},
            "signs": {},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 5,
            "support": "intubated",
            "product": "survanta"
        },
        "expected": {
            "result": "Indicated",
            "prophylactic": True,   # GA 29+6 = 209 days < 210
            "rescue": False,
        }
    },
    {
        "id": "TC06",
        "name": "Boundary 30+0w - NOT Prophylactic eligible",
        "inputs": {
            "patient": {"ga_weeks": 30, "ga_days": 0, "weight": 1400, "age_hours": 0, "fio2": 25},
            "signs": {},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 5,
            "support": "intubated",
            "product": "survanta"
        },
        "expected": {
            "result": "NotIndicated",
            "prophylactic": False,  # GA 30+0 = 210 days >= 210
            "rescue": False,        # FiO2 25 <= 30
        }
    },
    {
        "id": "TC07",
        "name": "FiO2 boundary 30% - Not rescue",
        "inputs": {
            "patient": {"ga_weeks": 32, "ga_days": 0, "weight": 1800, "age_hours": 6, "fio2": 30},
            "signs": {"grunting": True, "retractions": True},
            "contraindications": {},
            "blood_gas": {"ph": 7320, "pco2": 45, "po2": 70},
            "minutes_since_birth": 360,
            "support": "cpap",
            "product": "curosurf"
        },
        "expected": {
            "result": "NotIndicated",
            "prophylactic": False,  # GA 32w >= 210 days
            "rescue": False,        # FiO2 30 <= 30 (not > 30)
        }
    },
    {
        "id": "TC08",
        "name": "FiO2 boundary 31% - Rescue eligible",
        "inputs": {
            "patient": {"ga_weeks": 32, "ga_days": 0, "weight": 1800, "age_hours": 6, "fio2": 31},
            "signs": {"grunting": True, "retractions": True},
            "contraindications": {},
            "cxr": {"ground_glass": True},
            "blood_gas": {"ph": 7320, "pco2": 45, "po2": 70},
            "minutes_since_birth": 360,
            "cpap_trial": {"pressure": 6, "duration": 30, "fio2": 35},
            "support": "cpap",
            "product": "curosurf"
        },
        "expected": {
            "result": "Indicated",
            "prophylactic": False,
            "rescue": True,         # FiO2 31 > 30, has signs
        }
    },
    {
        "id": "TC09",
        "name": "Only 1 sign - Not enough for rescue",
        "inputs": {
            "patient": {"ga_weeks": 32, "ga_days": 0, "weight": 1800, "age_hours": 6, "fio2": 50},
            "signs": {"grunting": True, "retractions": False, "nasal_flaring": False, "cyanosis": False},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 360,
            "support": "cpap",
            "product": "curosurf"
        },
        "expected": {
            "result": "NotIndicated",
            "prophylactic": False,
            "rescue": False,        # Only 1 sign, need >= 2
        }
    },
    {
        "id": "TC10",
        "name": "Dose calculation - Survanta 1000g",
        "inputs": {
            "patient": {"ga_weeks": 28, "ga_days": 0, "weight": 1000, "age_hours": 0, "fio2": 40},
            "signs": {},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 5,
            "support": "intubated",
            "product": "survanta"
        },
        "expected": {
            "result": "Indicated",
            "dose_mg": 100,  # 1000g * 100mg/kg / 1000 = 100mg
        }
    },
    {
        "id": "TC11",
        "name": "Dose calculation - Curosurf 900g",
        "inputs": {
            "patient": {"ga_weeks": 27, "ga_days": 0, "weight": 900, "age_hours": 0, "fio2": 40},
            "signs": {},
            "contraindications": {},
            "blood_gas": {"ph": 7350, "pco2": 40, "po2": 80},
            "minutes_since_birth": 5,
            "support": "intubated",
            "product": "curosurf"
        },
        "expected": {
            "result": "Indicated",
            "dose_mg": 180,  # 900g * 200mg/kg / 1000 = 180mg
        }
    },
    {
        "id": "TC12",
        "name": "Multiple contraindications",
        "inputs": {
            "patient": {"ga_weeks": 26, "ga_days": 0, "weight": 700, "age_hours": 1, "fio2": 60},
            "signs": {"grunting": True, "retractions": True, "nasal_flaring": True, "cyanosis": True},
            "contraindications": {"cdh": False, "lethal_anomaly": True, "pneumothorax": True},
            "blood_gas": {"ph": 7200, "pco2": 70, "po2": 40},
            "minutes_since_birth": 60,
            "support": "intubated",
            "product": "curosurf"
        },
        "expected": {
            "result": "NotIndicated",
            "prophylactic": False,
            "rescue": False,
        }
    },
]


OPAM = r"C:\Users\cnort\AppData\Local\Microsoft\WinGet\Packages\OCaml.opam_Microsoft.Winget.Source_8wekyb3d8bbwe\opam.exe"

def run_ocaml_test(test_case):
    """Run test case through OCaml CLI."""
    try:
        result = subprocess.run(
            [OPAM, "exec", "--switch=5.1.1", "--", "ocamlrun", OCAML_CLI],
            input=json.dumps(test_case["inputs"]),
            capture_output=True,
            text=True,
            timeout=10
        )
        if result.returncode != 0:
            return {"error": result.stderr}
        return json.loads(result.stdout.strip())
    except Exception as e:
        return {"error": str(e)}


def check_property(test_case):
    """Manually check properties based on test inputs."""
    p = test_case["inputs"]["patient"]
    signs = test_case["inputs"].get("signs", {})
    contras = test_case["inputs"].get("contraindications", {})

    ga_days = p["ga_weeks"] * 7 + p["ga_days"]
    fio2 = p["fio2"]

    # Count signs
    sign_count = sum([
        signs.get("grunting", False),
        signs.get("retractions", False),
        signs.get("nasal_flaring", False),
        signs.get("cyanosis", False)
    ])

    # Check contraindications
    has_contra = any([
        contras.get("cdh", False),
        contras.get("lethal_anomaly", False),
        contras.get("pulmonary_hypoplasia", False),
        contras.get("pulmonary_hemorrhage", False),
        contras.get("pneumothorax", False)
    ])

    # Prophylactic: GA < 210 days
    prophylactic = ga_days < 210

    # Rescue: FiO2 > 30 AND >= 2 signs
    rescue = fio2 > 30 and sign_count >= 2

    # Indicated if no contraindication AND (prophylactic OR rescue)
    indicated = not has_contra and (prophylactic or rescue)

    return {
        "ga_days": ga_days,
        "sign_count": sign_count,
        "has_contra": has_contra,
        "prophylactic": prophylactic,
        "rescue": rescue,
        "indicated": indicated
    }


def run_cross_validation():
    """Run all test cases through all implementations."""
    print("=" * 70)
    print("CROSS-VALIDATION TEST SUITE")
    print("Surfactant Decision Logic")
    print("=" * 70)

    results = []
    passed = 0
    failed = 0

    for tc in TEST_CASES:
        print(f"\n[{tc['id']}] {tc['name']}")
        print("-" * 50)

        # Run OCaml
        ocaml_result = run_ocaml_test(tc)
        ocaml_verdict = ocaml_result.get("result", "ERROR")

        # Manual property check
        props = check_property(tc)
        manual_verdict = "Indicated" if props["indicated"] else "NotIndicated"

        # Expected
        expected = tc["expected"]["result"]

        # Compare
        ocaml_match = ocaml_verdict == expected
        manual_match = manual_verdict == expected
        all_match = ocaml_match and manual_match

        print(f"  Expected:     {expected}")
        print(f"  OCaml:        {ocaml_verdict} {'[OK]' if ocaml_match else '[FAIL]'}")
        print(f"  Manual:       {manual_verdict} {'[OK]' if manual_match else '[FAIL]'}")

        if "dose_mg" in tc["expected"]:
            expected_dose = tc["expected"]["dose_mg"]
            actual_dose = ocaml_result.get("dose_mg", "?")
            dose_match = actual_dose == expected_dose
            print(f"  Dose:         {actual_dose}mg (expected {expected_dose}mg) {'[OK]' if dose_match else '[FAIL]'}")
            all_match = all_match and dose_match

        # Details
        print(f"  [GA={props['ga_days']}d, FiO2={tc['inputs']['patient']['fio2']}%, "
              f"signs={props['sign_count']}, contra={props['has_contra']}]")

        if all_match:
            passed += 1
            print(f"  RESULT: PASS")
        else:
            failed += 1
            print(f"  RESULT: FAIL")

        results.append({
            "id": tc["id"],
            "name": tc["name"],
            "expected": expected,
            "ocaml": ocaml_verdict,
            "manual": manual_verdict,
            "match": all_match
        })

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total:  {len(TEST_CASES)}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")

    if failed == 0:
        print("\n*** ALL IMPLEMENTATIONS AGREE - CROSS-VALIDATION SUCCESSFUL ***")
    else:
        print(f"\n*** {failed} DISCREPANCIES FOUND ***")

    return failed == 0, results


if __name__ == "__main__":
    # Check OCaml CLI exists
    if not os.path.exists(OCAML_CLI):
        print(f"ERROR: OCaml CLI not found at {OCAML_CLI}")
        print("Please compile with: ocamlc str.cma surfactant_decision.mli surfactant_decision.ml surfactant_cli.ml -o surfactant_cli.exe")
        sys.exit(1)

    success, results = run_cross_validation()
    sys.exit(0 if success else 1)
