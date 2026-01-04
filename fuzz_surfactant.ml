(* fuzz_surfactant.ml - Fuzz testing for surfactant decision logic *)
(* Generates random valid ClinicalState values and tests invariants *)

open Surfactant_decision
open SurfactantDecision

(* Random generation seed *)
let () = Random.self_init ()

(* Generate random int in range [lo, hi] *)
let rand_range lo hi =
  lo + Random.int (hi - lo + 1)

(* Generate random bool *)
let rand_bool () =
  Random.bool ()

(* Generate random valid patient *)
let rand_patient () =
  { ga_weeks = rand_range 22 42;
    ga_days = rand_range 0 6;
    birth_weight = rand_range 200 6000;
    age_hours = rand_range 0 168;
    current_fio2 = rand_range 21 100 }

(* Generate random RDS signs *)
let rand_signs () =
  { grunting = rand_bool ();
    retractions = rand_bool ();
    nasal_flaring = rand_bool ();
    cyanosis_in_room_air = rand_bool () }

(* Generate random contraindications (mostly false for realistic distribution) *)
let rand_contraindications () =
  let prob_contra = 0.05 in (* 5% chance of each contraindication *)
  { congenital_diaphragmatic_hernia = Random.float 1.0 < prob_contra;
    lethal_anomaly = Random.float 1.0 < prob_contra;
    pulmonary_hypoplasia = Random.float 1.0 < prob_contra;
    active_pulmonary_hemorrhage = Random.float 1.0 < prob_contra;
    pneumothorax_untreated = Random.float 1.0 < prob_contra }

(* Generate random chest X-ray *)
let rand_cxr () =
  { ground_glass_opacity = rand_bool ();
    air_bronchograms = rand_bool ();
    low_lung_volumes = rand_bool ();
    reticulogranular_pattern = rand_bool () }

(* Generate random lung ultrasound *)
let rand_ultrasound () =
  { bilateral_white_lung = rand_bool ();
    absent_a_lines = rand_bool ();
    pleural_irregularity = rand_bool ();
    consolidations = rand_bool () }

(* Generate random imaging evidence *)
let rand_imaging () =
  let cxr = if rand_bool () then Some (rand_cxr ()) else None in
  let us = if rand_bool () then Some (rand_ultrasound ()) else None in
  { ie_cxr = cxr;
    ie_ultrasound = us;
    ie_clinical_judgement = rand_bool () }

(* Generate random blood gas *)
let rand_blood_gas () =
  { ph = rand_range 6800 7800;  (* pH 6.80 - 7.80 scaled *)
    pco2 = rand_range 10 150;
    po2 = rand_range 10 500 }

(* Generate random CPAP trial *)
let rand_cpap_trial () =
  { cpap_pressure_cmh2o = rand_range 0 20;
    cpap_duration_minutes = rand_range 0 360;
    fio2_on_cpap = rand_range 21 100 }

(* Generate random respiratory support *)
let rand_support () =
  match Random.int 3 with
  | 0 -> RoomAir
  | 1 -> CPAP
  | _ -> Intubated

(* Generate random clinical state *)
let rand_clinical_state () =
  let cpap = if rand_bool () then Some (rand_cpap_trial ()) else None in
  { cs_patient = rand_patient ();
    cs_signs = rand_signs ();
    cs_contraindications = rand_contraindications ();
    cs_imaging = rand_imaging ();
    cs_blood_gas = rand_blood_gas ();
    cs_minutes_since_birth = rand_range 0 1440; (* 0-24 hours *)
    cs_cpap_trial = cpap;
    cs_current_support = rand_support () }

(* ========== INVARIANT CHECKS ========== *)

(* Invariant 1: Valid patients should always get a definite result *)
let check_valid_patient_definite cs =
  let patient_valid = validate_patient cs.cs_patient in
  let result = recommend_surfactant_safe cs in
  if patient_valid then
    result <> InvalidPatient
  else
    true (* No constraint for invalid patients *)

(* Invariant 2: InvalidInput only for validation failures *)
let check_invalid_input cs =
  let result = recommend_surfactant_safe cs in
  match result with
  | InvalidInput ->
    (* InvalidInput means validation failed *)
    not (validate_clinical_state cs)
  | _ -> true

(* Invariant 3: Well infant should not be indicated *)
let check_well_infant cs =
  let ga_days = cs.cs_patient.ga_weeks * 7 + cs.cs_patient.ga_days in
  let fio2 = cs.cs_patient.current_fio2 in
  let result = recommend_surfactant_safe cs in
  (* GA >= 30 weeks (210 days) AND FiO2 <= 30 should not be Indicated *)
  if ga_days >= 210 && fio2 <= 30 then
    result <> Indicated
  else
    true

(* Invariant 4: Contraindication should block Indicated *)
let check_contraindication_blocks cs =
  let has_contra =
    cs.cs_contraindications.congenital_diaphragmatic_hernia ||
    cs.cs_contraindications.lethal_anomaly ||
    cs.cs_contraindications.pulmonary_hypoplasia ||
    cs.cs_contraindications.active_pulmonary_hemorrhage ||
    cs.cs_contraindications.pneumothorax_untreated in
  let result = recommend_surfactant_safe cs in
  if has_contra then
    result <> Indicated
  else
    true

(* Invariant 5: Dose calculation is always positive for valid weights *)
let check_dose_positive () =
  let weight = rand_range 200 6000 in
  let products = [Survanta; Curosurf; Infasurf] in
  List.for_all (fun prod ->
    let dose = calc_initial_dose prod weight in
    dose > 0
  ) products

(* Invariant 6: Dose is bounded (never exceeds 600mg for any product up to 3kg) *)
let check_dose_bounded () =
  let weight = rand_range 200 3000 in (* Realistic preterm range *)
  let products = [Survanta; Curosurf; Infasurf] in
  List.for_all (fun prod ->
    let dose = calc_initial_dose prod weight in
    dose <= 601  (* Allow slight overage due to rounding *)
  ) products

(* ========== FUZZ RUNNER ========== *)
let run_fuzz_tests n =
  Printf.printf "Running %d fuzz iterations...\n" n;
  let failures = ref 0 in
  let invariant_failures = Array.make 6 0 in

  for i = 1 to n do
    let cs = rand_clinical_state () in

    if not (check_valid_patient_definite cs) then begin
      incr failures;
      invariant_failures.(0) <- invariant_failures.(0) + 1
    end;

    if not (check_invalid_input cs) then begin
      incr failures;
      invariant_failures.(1) <- invariant_failures.(1) + 1
    end;

    if not (check_well_infant cs) then begin
      incr failures;
      invariant_failures.(2) <- invariant_failures.(2) + 1
    end;

    if not (check_contraindication_blocks cs) then begin
      incr failures;
      invariant_failures.(3) <- invariant_failures.(3) + 1
    end;

    if not (check_dose_positive ()) then begin
      incr failures;
      invariant_failures.(4) <- invariant_failures.(4) + 1
    end;

    if not (check_dose_bounded ()) then begin
      incr failures;
      invariant_failures.(5) <- invariant_failures.(5) + 1
    end;

    if i mod 1000 = 0 then
      Printf.printf "  Progress: %d/%d iterations\n%!" i n
  done;

  Printf.printf "\n=== Fuzz Test Results ===\n";
  Printf.printf "Total iterations: %d\n" n;
  Printf.printf "Total failures: %d\n" !failures;
  Printf.printf "\nInvariant breakdown:\n";
  Printf.printf "  1. Valid patient definite:    %d failures\n" invariant_failures.(0);
  Printf.printf "  2. InvalidInput validation:   %d failures\n" invariant_failures.(1);
  Printf.printf "  3. Well infant not indicated: %d failures\n" invariant_failures.(2);
  Printf.printf "  4. Contraindication blocks:   %d failures\n" invariant_failures.(3);
  Printf.printf "  5. Dose positive:             %d failures\n" invariant_failures.(4);
  Printf.printf "  6. Dose bounded:              %d failures\n" invariant_failures.(5);

  if !failures = 0 then begin
    Printf.printf "\nALL INVARIANTS HELD\n";
    0
  end else begin
    Printf.printf "\nSOME INVARIANTS VIOLATED\n";
    1
  end

(* ========== MAIN ========== *)
let () =
  Printf.printf "Surfactant Decision Logic - Fuzz Testing\n";
  Printf.printf "=========================================\n\n";

  let num_iterations =
    if Array.length Sys.argv > 1 then
      int_of_string Sys.argv.(1)
    else
      1000  (* Default to 1000 for quick runs *)
  in

  let exit_code = run_fuzz_tests num_iterations in
  exit exit_code
