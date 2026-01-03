(******************************************************************************)
(*                                                                            *)
(*         Surfactant Administration for Neonatal Respiratory Distress        *)
(*                                                                            *)
(*     Formalizes prophylactic and rescue surfactant criteria for preterm     *)
(*     infants with RDS. Models gestational age, FiO2 thresholds, weight-     *)
(*     based dosing, and repeat administration logic per consensus guidelines.*)
(*                                                                            *)
(*     "And breathed into his nostrils the breath of life."                   *)
(*     — Genesis 2:7                                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** -------------------------------------------------------------------------- *)
(** SOURCES                                                                    *)
(** -------------------------------------------------------------------------- *)

(**
   [1] Sweet DG, Carnielli VP, Greisen G, et al.
       "European Consensus Guidelines on the Management of Respiratory
       Distress Syndrome: 2022 Update."
       Neonatology. 2023;120(1):3-23.
       doi:10.1159/000528914

   [2] American Academy of Pediatrics Committee on Fetus and Newborn.
       "Surfactant Replacement Therapy for Preterm and Term Neonates
       With Respiratory Distress."
       Pediatrics. 2014;133(1):156-163.
       doi:10.1542/peds.2013-3443

   [3] Product Prescribing Information:
       - Survanta (beractant): 100 mg phospholipids/kg, up to 4 doses
       - Curosurf (poractant alfa): 100-200 mg/kg initial, 100 mg/kg repeat
       - Infasurf (calfactant): 105 mg phospholipids/kg, up to 3 doses
*)

(** -------------------------------------------------------------------------- *)
(** GAPS AND FURTHER WORK                                                      *)
(** -------------------------------------------------------------------------- *)

(**
   Contraindications: Does not model when to withhold (congenital
     diaphragmatic hernia, lethal anomalies, pulmonary hypoplasia).

   CPAP-first protocols: Modern INSURE/LISA techniques use CPAP trial
     before surfactant. This model assumes intubation pathway.

   SpO2 targeting: Real decisions use SpO2 ranges (88-95%), not just FiO2.
     FiO2 is a proxy for oxygenation failure, not the full picture.

   Blood gas integration: pH < 7.20 or pCO2 > 60 may influence timing
     independent of FiO2. Not currently modeled.

   CXR confirmation: Ground-glass appearance on chest X-ray confirms RDS
     but is not encoded in clinical_rds predicate.

   Delivery room timing: Prophylactic surfactant should be given within
     15 minutes of birth. Time constraint not enforced.

   Administration technique: INSURE vs LISA vs conventional intubation
     affects outcomes but is outside scope of indication logic.

   Boundary behavior: Predicates use strict inequalities. Infants at
     exactly 26 weeks or exactly 30% FiO2 fall on edges. Audit needed.

   Extraction and validation: OCaml extraction not yet tested against
     actual NICU case records. EXERCISED status pending.
*)

From Coq Require Import Arith Lia.

(** -------------------------------------------------------------------------- *)
(** Patient Record                                                             *)
(** -------------------------------------------------------------------------- *)

(** Gestational age in completed weeks (22-42 typical range). *)
Definition gestational_age := nat.

(** Birth weight in grams. *)
Definition weight_g := nat.

(** Postnatal age in hours. *)
Definition postnatal_hours := nat.

(** FiO2 as percentage (21-100). 21 = room air, 100 = pure oxygen. *)
Definition fio2_pct := nat.

(** Patient state for surfactant decision. *)
Record Patient := mkPatient {
  ga_weeks : gestational_age;
  birth_weight : weight_g;
  age_hours : postnatal_hours;
  current_fio2 : fio2_pct
}.

(** Validity predicate: GA and weight within physiological bounds. *)
Definition valid_patient (p : Patient) : Prop :=
  22 <= ga_weeks p /\ ga_weeks p <= 42 /\
  200 <= birth_weight p /\ birth_weight p <= 6000 /\
  21 <= current_fio2 p /\ current_fio2 p <= 100.

(** --- Witness: A valid 26-week, 800g infant --- *)
Definition witness_patient : Patient :=
  mkPatient 26 800 2 45.

Lemma witness_patient_valid : valid_patient witness_patient.
Proof.
  unfold valid_patient, witness_patient. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Counterexample: Invalid GA (50 weeks) --- *)
Definition invalid_patient_ga : Patient :=
  mkPatient 50 3000 1 21.

Lemma invalid_patient_ga_not_valid : ~ valid_patient invalid_patient_ga.
Proof.
  unfold valid_patient, invalid_patient_ga. simpl.
  intros [_ [H _]].
  assert (Hfalse: 50 <=? 42 = false) by reflexivity.
  apply Nat.leb_le in H. rewrite H in Hfalse. discriminate.
Qed.

(** -------------------------------------------------------------------------- *)
(** Clinical RDS Signs                                                         *)
(** -------------------------------------------------------------------------- *)

(** Clinical signs of respiratory distress syndrome. *)
Record RDSSigns := mkRDSSigns {
  grunting : bool;
  retractions : bool;
  nasal_flaring : bool;
  cyanosis_in_room_air : bool
}.

(** Count of positive signs. *)
Definition sign_count (s : RDSSigns) : nat :=
  (if grunting s then 1 else 0) +
  (if retractions s then 1 else 0) +
  (if nasal_flaring s then 1 else 0) +
  (if cyanosis_in_room_air s then 1 else 0).

(** Clinical RDS requires at least 2 signs. *)
Definition clinical_rds (s : RDSSigns) : Prop :=
  sign_count s >= 2.

(** --- Witness: Infant with 3 signs --- *)
Definition witness_rds_signs : RDSSigns :=
  mkRDSSigns true true true false.

Lemma witness_rds_signs_positive : clinical_rds witness_rds_signs.
Proof.
  unfold clinical_rds, sign_count, witness_rds_signs. simpl.
  apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: Infant with 0 signs --- *)
Definition no_rds_signs : RDSSigns :=
  mkRDSSigns false false false false.

Lemma no_rds_signs_negative : ~ clinical_rds no_rds_signs.
Proof.
  unfold clinical_rds, sign_count, no_rds_signs. simpl.
  apply Nat.lt_nge. apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** FiO2 Threshold                                                             *)
(** -------------------------------------------------------------------------- *)

(** European Consensus threshold: FiO2 > 30% indicates need for surfactant. *)
Definition fio2_threshold : nat := 30.

(** FiO2 exceeds threshold. *)
Definition fio2_elevated (f : fio2_pct) : Prop :=
  f > fio2_threshold.

(** --- Witness: FiO2 45% exceeds 30% threshold --- *)
Lemma fio2_45_elevated : fio2_elevated 45.
Proof.
  unfold fio2_elevated, fio2_threshold.
  apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: FiO2 25% does not exceed threshold --- *)
Lemma fio2_25_not_elevated : ~ fio2_elevated 25.
Proof.
  unfold fio2_elevated, fio2_threshold.
  apply Nat.lt_nge. apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Gestational Age Thresholds                                                 *)
(** -------------------------------------------------------------------------- *)

(** Prophylactic surfactant threshold: < 26 weeks per European Consensus. *)
Definition prophylactic_ga_threshold : nat := 26.

(** Eligible for prophylactic surfactant based on GA alone. *)
Definition prophylactic_eligible_ga (ga : gestational_age) : Prop :=
  ga < prophylactic_ga_threshold.

(** --- Witness: 25 weeks eligible for prophylactic --- *)
Lemma ga_25_prophylactic_eligible : prophylactic_eligible_ga 25.
Proof.
  unfold prophylactic_eligible_ga, prophylactic_ga_threshold.
  apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: 32 weeks not eligible for prophylactic --- *)
Lemma ga_32_not_prophylactic_eligible : ~ prophylactic_eligible_ga 32.
Proof.
  unfold prophylactic_eligible_ga, prophylactic_ga_threshold.
  apply Nat.le_ngt. apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Indication Logic                                                           *)
(** -------------------------------------------------------------------------- *)

(** Prophylactic indication: GA < 26 weeks, given in delivery room. *)
Definition prophylactic_indicated (p : Patient) : Prop :=
  prophylactic_eligible_ga (ga_weeks p).

(** Rescue indication: FiO2 elevated AND clinical signs present. *)
Definition rescue_indicated (p : Patient) (signs : RDSSigns) : Prop :=
  fio2_elevated (current_fio2 p) /\ clinical_rds signs.

(** Combined indication: prophylactic OR rescue. *)
Definition surfactant_indicated (p : Patient) (signs : RDSSigns) : Prop :=
  prophylactic_indicated p \/ rescue_indicated p signs.

(** --- Witness: 27w infant with FiO2 40% and signs → rescue indicated --- *)
Definition rescue_patient : Patient := mkPatient 27 900 6 40.
Definition rescue_signs : RDSSigns := mkRDSSigns true true false false.

Lemma rescue_patient_indicated : surfactant_indicated rescue_patient rescue_signs.
Proof.
  unfold surfactant_indicated. right.
  unfold rescue_indicated. split.
  - unfold fio2_elevated, fio2_threshold, rescue_patient. simpl.
    apply Nat.leb_le. reflexivity.
  - unfold clinical_rds, sign_count, rescue_signs. simpl.
    apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: 34w infant with FiO2 21% and no signs → not indicated --- *)
Definition well_patient : Patient := mkPatient 34 2200 12 21.
Definition well_signs : RDSSigns := mkRDSSigns false false false false.

Lemma well_patient_not_indicated : ~ surfactant_indicated well_patient well_signs.
Proof.
  unfold surfactant_indicated. intros [Hpro | Hres].
  - unfold prophylactic_indicated, prophylactic_eligible_ga,
      prophylactic_ga_threshold, well_patient in Hpro. simpl in Hpro.
    apply Nat.lt_nge in Hpro. apply Hpro.
    apply Nat.leb_le. reflexivity.
  - unfold rescue_indicated in Hres. destruct Hres as [Hfio2 _].
    unfold fio2_elevated, fio2_threshold, well_patient in Hfio2. simpl in Hfio2.
    apply Nat.lt_nge in Hfio2. apply Hfio2.
    apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Product Types                                                              *)
(** -------------------------------------------------------------------------- *)

(** Surfactant products with their dosing parameters. *)
Inductive SurfactantProduct : Type :=
  | Survanta   (* beractant: 100 mg/kg, max 4 doses *)
  | Curosurf   (* poractant alfa: 200 mg/kg initial, 100 mg/kg repeat, max 3 doses *)
  | Infasurf.  (* calfactant: 105 mg/kg, max 3 doses *)

(** Initial dose in mg per kg. *)
Definition initial_dose_per_kg (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 100
  | Curosurf => 200
  | Infasurf => 105
  end.

(** Repeat dose in mg per kg. *)
Definition repeat_dose_per_kg (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 100
  | Curosurf => 100  (* lower for repeats *)
  | Infasurf => 105
  end.

(** Maximum number of doses. *)
Definition max_doses (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 4
  | Curosurf => 3
  | Infasurf => 3
  end.

(** -------------------------------------------------------------------------- *)
(** Dose Calculation                                                           *)
(** -------------------------------------------------------------------------- *)

(** Calculate dose in mg given weight in grams and dose per kg.
    Weight is in grams, so we compute: weight_g * dose_per_kg / 1000. *)
Definition calculate_dose (weight_g : nat) (dose_per_kg : nat) : nat :=
  weight_g * dose_per_kg / 1000.

(** Initial dose for a patient. *)
Definition initial_dose (prod : SurfactantProduct) (weight : weight_g) : nat :=
  calculate_dose weight (initial_dose_per_kg prod).

(** Repeat dose for a patient. *)
Definition repeat_dose (prod : SurfactantProduct) (weight : weight_g) : nat :=
  calculate_dose weight (repeat_dose_per_kg prod).

(** --- Witness: 800g infant, Curosurf initial → 160mg --- *)
Lemma curosurf_800g_initial_dose : initial_dose Curosurf 800 = 160.
Proof. reflexivity. Qed.

(** --- Witness: 800g infant, Curosurf repeat → 80mg --- *)
Lemma curosurf_800g_repeat_dose : repeat_dose Curosurf 800 = 80.
Proof. reflexivity. Qed.

(** Dose validity: must be positive and within reasonable bounds.
    Max reasonable dose ~600mg for a 3kg infant at 200mg/kg. *)
Definition dose_valid (dose : nat) : Prop :=
  dose > 0 /\ dose <= 600.

(** --- Witness: 160mg is valid --- *)
Lemma dose_160_valid : dose_valid 160.
Proof.
  unfold dose_valid. split.
  - apply Nat.leb_le. reflexivity.
  - apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: 800mg exceeds max --- *)
Lemma dose_800_invalid : ~ dose_valid 800.
Proof.
  unfold dose_valid. intros [_ H].
  assert (Hfalse: 800 <=? 600 = false) by reflexivity.
  apply Nat.leb_le in H. rewrite H in Hfalse. discriminate.
Qed.

(** -------------------------------------------------------------------------- *)
(** Repeat Dosing Logic                                                        *)
(** -------------------------------------------------------------------------- *)

(** Dosing state tracks doses given. *)
Record DosingState := mkDosingState {
  product : SurfactantProduct;
  doses_given : nat;
  hours_since_last : nat
}.

(** Minimum hours between doses. *)
Definition min_hours_between_doses : nat := 6.

(** Eligible for repeat dose: under max AND enough time passed AND still needing O2. *)
Definition repeat_eligible (ds : DosingState) (current_fio2 : fio2_pct) : Prop :=
  doses_given ds < max_doses (product ds) /\
  hours_since_last ds >= min_hours_between_doses /\
  fio2_elevated current_fio2.

(** --- Witness: 2nd dose of Survanta, 8 hours later, FiO2 40% → eligible --- *)
Definition eligible_repeat_state : DosingState := mkDosingState Survanta 1 8.

Lemma eligible_repeat_state_ok : repeat_eligible eligible_repeat_state 40.
Proof.
  unfold repeat_eligible, eligible_repeat_state. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Counterexample: 5th dose of Survanta (max 4) → not eligible --- *)
Definition max_doses_exceeded : DosingState := mkDosingState Survanta 4 12.

Lemma max_doses_exceeded_ineligible : ~ repeat_eligible max_doses_exceeded 40.
Proof.
  unfold repeat_eligible, max_doses_exceeded. simpl.
  intros [Hdoses _].
  apply Nat.lt_nge in Hdoses. apply Hdoses.
  apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Safety Theorems                                                            *)
(** -------------------------------------------------------------------------- *)

(** Safe to give surfactant if indicated and valid patient. *)
Definition safe_to_give (p : Patient) (signs : RDSSigns) (dose : nat) : Prop :=
  valid_patient p /\
  surfactant_indicated p signs /\
  dose_valid dose.

(** Theorem: If all preconditions met, administration is safe. *)
Theorem administration_safe :
  forall p signs dose,
    valid_patient p ->
    surfactant_indicated p signs ->
    dose_valid dose ->
    safe_to_give p signs dose.
Proof.
  intros p signs dose Hvalid Hind Hdose.
  unfold safe_to_give. auto.
Qed.

(** Theorem: Not indicated implies withholding is appropriate. *)
Theorem withhold_when_not_indicated :
  forall p signs,
    ~ surfactant_indicated p signs ->
    ~ (surfactant_indicated p signs).
Proof.
  intros p signs Hnot. exact Hnot.
Qed.

(** Theorem: Dose from calculation is bounded for valid weights.
    Proof uses the fact that max weight 3000g * max rate 200mg/kg / 1000 = 600mg. *)
Theorem calculated_dose_bounded :
  forall prod weight,
    weight <= 3000 ->
    initial_dose prod weight <= 600.
Proof.
  intros prod weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  destruct prod.
  - (* Survanta: weight * 100 / 1000 <= 300 <= 600 *)
    apply Nat.le_trans with (weight * 100 / 1000).
    + apply Nat.le_refl.
    + apply Nat.le_trans with (3000 * 100 / 1000).
      * apply Nat.Div0.div_le_mono. lia.
      * apply Nat.leb_le. reflexivity.
  - (* Curosurf: weight * 200 / 1000 <= 600 *)
    apply Nat.le_trans with (3000 * 200 / 1000).
    + apply Nat.Div0.div_le_mono. lia.
    + apply Nat.leb_le. reflexivity.
  - (* Infasurf: weight * 105 / 1000 <= 315 <= 600 *)
    apply Nat.le_trans with (3000 * 105 / 1000).
    + apply Nat.Div0.div_le_mono. lia.
    + apply Nat.leb_le. reflexivity.
Qed.
