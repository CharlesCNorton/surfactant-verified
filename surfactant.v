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
(** ROADMAP                                                                    *)
(** -------------------------------------------------------------------------- *)

(**
   [ ] Rescue indication (FiO2 + clinical signs)
   [ ] Combined indication predicate with witness/counterexample
   [ ] Product type (Survanta, Curosurf, Infasurf)
   [ ] Weight-based dose calculation
   [ ] Dose validity bounds with witness/counterexample
   [ ] Repeat dosing: time since last dose
   [ ] Repeat dosing: persistent FiO2 requirement
   [ ] Dose count tracking and max doses with witness/counterexample
   [ ] Safety theorem: indicated ∧ ¬contraindicated → safe_to_give
   [ ] Safety theorem: ¬indicated → withhold_appropriate
   [ ] Safety theorem: dose_in_bounds → no_overdose
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
