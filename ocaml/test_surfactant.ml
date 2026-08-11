(* test_surfactant.ml - Unit tests for surfactant decision logic *)
(* Run with: ocamlc surfactant_decision.mli surfactant_decision.ml test_surfactant.ml -o test_surfactant.exe *)

open Surfactant_decision
open SurfactantDecision

(* Test counters *)
let tests_run = ref 0
let tests_passed = ref 0

let test name expected actual =
  incr tests_run;
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  PASS: %s\n" name
  end else begin
    Printf.printf "  FAIL: %s (expected %s, got %s)\n" name
      (if expected then "true" else "false")
      (if actual then "true" else "false")
  end

let test_int name expected actual =
  incr tests_run;
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  PASS: %s\n" name
  end else begin
    Printf.printf "  FAIL: %s (expected %d, got %d)\n" name expected actual
  end

let test_result name expected actual =
  incr tests_run;
  let result_to_string = function
    | InvalidInput -> "InvalidInput"
    | InvalidPatient -> "InvalidPatient"
    | NotIndicated -> "NotIndicated"
    | Indicated -> "Indicated"
  in
  if expected = actual then begin
    incr tests_passed;
    Printf.printf "  PASS: %s\n" name
  end else begin
    Printf.printf "  FAIL: %s (expected %s, got %s)\n" name
      (result_to_string expected)
      (result_to_string actual)
  end

(* Helper to create patients *)
let make_patient ~ga_weeks ~ga_days ~weight ~age_hours ~fio2 =
  { ga_weeks; ga_days; birth_weight = weight; age_hours; current_fio2 = fio2 }

(* Helper to create RDS signs *)
let make_signs ~grunting ~retractions ~nasal_flaring ~cyanosis =
  { grunting; retractions; nasal_flaring; cyanosis_in_room_air = cyanosis }

(* Helper to create contraindications *)
let no_contras =
  { congenital_diaphragmatic_hernia = false;
    lethal_anomaly = false;
    pulmonary_hypoplasia = false;
    active_pulmonary_hemorrhage = false;
    pneumothorax_untreated = false }

let cdh_present =
  { congenital_diaphragmatic_hernia = true;
    lethal_anomaly = false;
    pulmonary_hypoplasia = false;
    active_pulmonary_hemorrhage = false;
    pneumothorax_untreated = false }

(* Helper to create CPAP trial *)
let make_cpap ~pressure ~duration ~fio2 =
  { cpap_pressure_cmh2o = pressure;
    cpap_duration_minutes = duration;
    fio2_on_cpap = fio2 }

(* Helper to create chest X-ray *)
let make_cxr ~ground_glass ~bronchograms ~low_volumes ~reticgran =
  { ground_glass_opacity = ground_glass;
    air_bronchograms = bronchograms;
    low_lung_volumes = low_volumes;
    reticulogranular_pattern = reticgran }

(* Helper to create imaging evidence *)
let make_imaging ?cxr ?ultrasound ?(clinical_judgement=false) () =
  { ie_cxr = cxr;
    ie_ultrasound = ultrasound;
    ie_clinical_judgement = clinical_judgement }

(* Helper to create blood gas *)
let make_gas ~ph ~pco2 ~po2 =
  { ph; pco2; po2 }

(* Helper to create clinical state *)
let make_clinical_state patient signs contras imaging gas minutes_birth cpap support =
  { cs_patient = patient;
    cs_signs = signs;
    cs_contraindications = contras;
    cs_imaging = imaging;
    cs_blood_gas = gas;
    cs_minutes_since_birth = minutes_birth;
    cs_cpap_trial = cpap;
    cs_current_support = support }

(* ========== PATIENT VALIDATION TESTS ========== *)
let test_patient_validation () =
  Printf.printf "\n=== Patient Validation Tests ===\n";

  (* Valid patient *)
  let valid = make_patient ~ga_weeks:28 ~ga_days:3 ~weight:1000 ~age_hours:2 ~fio2:40 in
  test "valid patient 28+3w, 1000g" true (validate_patient valid);

  (* Edge cases - minimum GA *)
  let min_ga = make_patient ~ga_weeks:22 ~ga_days:0 ~weight:400 ~age_hours:1 ~fio2:30 in
  test "min GA 22+0w valid" true (validate_patient min_ga);

  (* Edge cases - maximum GA *)
  let max_ga = make_patient ~ga_weeks:42 ~ga_days:0 ~weight:4000 ~age_hours:1 ~fio2:21 in
  test "max GA 42+0w valid" true (validate_patient max_ga);

  (* Edge cases - minimum weight *)
  let min_wt = make_patient ~ga_weeks:24 ~ga_days:0 ~weight:200 ~age_hours:1 ~fio2:30 in
  test "min weight 200g valid" true (validate_patient min_wt);

  (* Edge cases - maximum weight *)
  let max_wt = make_patient ~ga_weeks:40 ~ga_days:0 ~weight:6000 ~age_hours:1 ~fio2:21 in
  test "max weight 6000g valid" true (validate_patient max_wt);

  (* Invalid: GA too low *)
  let low_ga = make_patient ~ga_weeks:21 ~ga_days:6 ~weight:500 ~age_hours:1 ~fio2:30 in
  test "GA 21+6w invalid (too low)" false (validate_patient low_ga);

  (* Invalid: GA too high *)
  let high_ga = make_patient ~ga_weeks:43 ~ga_days:0 ~weight:4000 ~age_hours:1 ~fio2:21 in
  test "GA 43+0w invalid (too high)" false (validate_patient high_ga);

  (* Invalid: ga_days > 6 *)
  let bad_days = make_patient ~ga_weeks:28 ~ga_days:7 ~weight:1000 ~age_hours:1 ~fio2:30 in
  test "ga_days=7 invalid" false (validate_patient bad_days);

  (* Invalid: weight too low *)
  let low_wt = make_patient ~ga_weeks:28 ~ga_days:0 ~weight:199 ~age_hours:1 ~fio2:30 in
  test "weight 199g invalid (too low)" false (validate_patient low_wt);

  (* Invalid: weight too high *)
  let high_wt = make_patient ~ga_weeks:40 ~ga_days:0 ~weight:6001 ~age_hours:1 ~fio2:21 in
  test "weight 6001g invalid (too high)" false (validate_patient high_wt);

  (* Invalid: FiO2 too low *)
  let low_fio2 = make_patient ~ga_weeks:28 ~ga_days:0 ~weight:1000 ~age_hours:1 ~fio2:20 in
  test "FiO2 20% invalid (too low)" false (validate_patient low_fio2);

  (* Invalid: FiO2 too high *)
  let high_fio2 = make_patient ~ga_weeks:28 ~ga_days:0 ~weight:1000 ~age_hours:1 ~fio2:101 in
  test "FiO2 101% invalid (too high)" false (validate_patient high_fio2)

(* ========== DOSE CALCULATION TESTS ========== *)
let test_dose_calculation () =
  Printf.printf "\n=== Dose Calculation Tests ===\n";

  (* Survanta: 100 mg/kg *)
  test_int "Survanta 1000g initial = 100mg" 100 (calc_initial_dose Survanta 1000);
  test_int "Survanta 800g initial = 80mg" 80 (calc_initial_dose Survanta 800);
  test_int "Survanta 849g initial = 85mg (rounded)" 85 (calc_initial_dose Survanta 849);

  (* Curosurf: 200 mg/kg initial, 100 mg/kg repeat *)
  test_int "Curosurf 1000g initial = 200mg" 200 (calc_initial_dose Curosurf 1000);
  test_int "Curosurf 800g initial = 160mg" 160 (calc_initial_dose Curosurf 800);
  test_int "Curosurf 1000g repeat = 100mg" 100 (calc_repeat_dose Curosurf 1000);

  (* Infasurf: 105 mg/kg *)
  test_int "Infasurf 1000g initial = 105mg" 105 (calc_initial_dose Infasurf 1000);
  test_int "Infasurf 800g initial = 84mg" 84 (calc_initial_dose Infasurf 800)

(* ========== RECOMMENDATION TESTS ========== *)
let test_recommendations () =
  Printf.printf "\n=== Recommendation Tests ===\n";

  (* Imaging evidence *)
  let normal_imaging = make_imaging () in
  let rds_cxr = make_cxr ~ground_glass:true ~bronchograms:true
                         ~low_volumes:true ~reticgran:false in
  let rds_imaging = make_imaging ~cxr:rds_cxr () in

  let normal_gas = make_gas ~ph:7350 ~pco2:40 ~po2:80 in
  let failed_cpap = make_cpap ~pressure:7 ~duration:30 ~fio2:50 in

  (* Well infant - should NOT be indicated *)
  let well_patient = make_patient ~ga_weeks:34 ~ga_days:0 ~weight:2200 ~age_hours:12 ~fio2:21 in
  let well_signs = make_signs ~grunting:false ~retractions:false ~nasal_flaring:false ~cyanosis:false in
  let well_state = make_clinical_state well_patient well_signs no_contras
                     normal_imaging normal_gas 720 None RoomAir in
  test_result "well infant not indicated" NotIndicated (recommend_surfactant_safe well_state);

  (* Preterm with RDS signs and failed CPAP - should be indicated *)
  let rds_patient = make_patient ~ga_weeks:27 ~ga_days:0 ~weight:900 ~age_hours:6 ~fio2:45 in
  let rds_signs = make_signs ~grunting:true ~retractions:true ~nasal_flaring:false ~cyanosis:false in
  let rds_state = make_clinical_state rds_patient rds_signs no_contras
                    rds_imaging normal_gas 360 (Some failed_cpap) CPAP in
  test_result "preterm with RDS indicated" Indicated (recommend_surfactant_safe rds_state);

  (* Contraindication blocks *)
  let cdh_state = make_clinical_state rds_patient rds_signs cdh_present
                    rds_imaging normal_gas 360 (Some failed_cpap) CPAP in
  test_result "CDH blocks indication" NotIndicated (recommend_surfactant_safe cdh_state);

  (* Prophylactic case: very preterm, intubated, within window *)
  let prophylactic_patient = make_patient ~ga_weeks:26 ~ga_days:0 ~weight:750 ~age_hours:0 ~fio2:40 in
  let no_signs = make_signs ~grunting:false ~retractions:false ~nasal_flaring:false ~cyanosis:false in
  let prophylactic_state = make_clinical_state prophylactic_patient no_signs no_contras
                             normal_imaging normal_gas 5 None Intubated in
  test_result "prophylactic 26w intubated" Indicated (recommend_surfactant_safe prophylactic_state);

  (* Edge: 30+0w NOT eligible for prophylactic *)
  let thirty_week = make_patient ~ga_weeks:30 ~ga_days:0 ~weight:1400 ~age_hours:0 ~fio2:25 in
  let thirty_state = make_clinical_state thirty_week no_signs no_contras
                       normal_imaging normal_gas 5 None Intubated in
  test_result "30+0w not prophylactic" NotIndicated (recommend_surfactant_safe thirty_state);

  (* Edge: 29+6w IS eligible for prophylactic *)
  let twentynine_six = make_patient ~ga_weeks:29 ~ga_days:6 ~weight:1350 ~age_hours:0 ~fio2:25 in
  let twentynine_state = make_clinical_state twentynine_six no_signs no_contras
                           normal_imaging normal_gas 5 None Intubated in
  test_result "29+6w prophylactic eligible" Indicated (recommend_surfactant_safe twentynine_state)

(* ========== CLINICAL RDS TESTS ========== *)
let test_clinical_rds () =
  Printf.printf "\n=== Clinical RDS Detection Tests ===\n";

  let no_signs = make_signs ~grunting:false ~retractions:false ~nasal_flaring:false ~cyanosis:false in
  let one_sign = make_signs ~grunting:true ~retractions:false ~nasal_flaring:false ~cyanosis:false in
  let two_signs = make_signs ~grunting:true ~retractions:true ~nasal_flaring:false ~cyanosis:false in
  let all_signs = make_signs ~grunting:true ~retractions:true ~nasal_flaring:true ~cyanosis:true in

  test "0 signs = no RDS" false (clinical_rds_dec no_signs);
  test "1 sign = no RDS" false (clinical_rds_dec one_sign);
  test "2 signs = RDS" true (clinical_rds_dec two_signs);
  test "4 signs = RDS" true (clinical_rds_dec all_signs);

  test_int "sign_count 0" 0 (sign_count_dec no_signs);
  test_int "sign_count 1" 1 (sign_count_dec one_sign);
  test_int "sign_count 2" 2 (sign_count_dec two_signs);
  test_int "sign_count 4" 4 (sign_count_dec all_signs)

(* ========== FIO2 THRESHOLD TESTS ========== *)
let test_fio2_threshold () =
  Printf.printf "\n=== FiO2 Threshold Tests ===\n";

  test "FiO2 30% not elevated" false (fio2_elevated_dec 30);
  test "FiO2 31% elevated" true (fio2_elevated_dec 31);
  test "FiO2 21% not elevated" false (fio2_elevated_dec 21);
  test "FiO2 50% elevated" true (fio2_elevated_dec 50)

(* ========== MAIN ========== *)
let () =
  Printf.printf "Surfactant Decision Logic - Unit Test Suite\n";
  Printf.printf "============================================\n";

  test_patient_validation ();
  test_dose_calculation ();
  test_recommendations ();
  test_clinical_rds ();
  test_fio2_threshold ();

  Printf.printf "\n============================================\n";
  Printf.printf "Results: %d/%d tests passed\n" !tests_passed !tests_run;
  if !tests_passed = !tests_run then
    Printf.printf "ALL TESTS PASSED\n"
  else
    Printf.printf "SOME TESTS FAILED\n";
  exit (if !tests_passed = !tests_run then 0 else 1)
