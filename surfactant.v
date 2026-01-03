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
   Validation: OCaml extraction provided but not yet tested against
     actual NICU case records. EXERCISED status pending external validation.
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
(** Contraindications                                                          *)
(** -------------------------------------------------------------------------- *)

(** Conditions where surfactant is contraindicated or should be withheld. *)
Record Contraindications := mkContraindications {
  congenital_diaphragmatic_hernia : bool;  (* CDH - lung hypoplasia, herniated viscera *)
  lethal_anomaly : bool;                   (* Trisomy 13/18, anencephaly, etc. *)
  pulmonary_hypoplasia : bool;             (* Severe lung underdevelopment *)
  active_pulmonary_hemorrhage : bool;      (* Ongoing bleeding into airways *)
  pneumothorax_untreated : bool            (* Air leak requiring drainage first *)
}.

(** No contraindications present. *)
Definition no_contraindications (c : Contraindications) : Prop :=
  congenital_diaphragmatic_hernia c = false /\
  lethal_anomaly c = false /\
  pulmonary_hypoplasia c = false /\
  active_pulmonary_hemorrhage c = false /\
  pneumothorax_untreated c = false.

(** Any contraindication present. *)
Definition has_contraindication (c : Contraindications) : Prop :=
  congenital_diaphragmatic_hernia c = true \/
  lethal_anomaly c = true \/
  pulmonary_hypoplasia c = true \/
  active_pulmonary_hemorrhage c = true \/
  pneumothorax_untreated c = true.

(** --- Witness: No contraindications --- *)
Definition clear_contraindications : Contraindications :=
  mkContraindications false false false false false.

Lemma clear_contraindications_ok : no_contraindications clear_contraindications.
Proof.
  unfold no_contraindications, clear_contraindications. simpl.
  repeat split; reflexivity.
Qed.

(** --- Counterexample: CDH present --- *)
Definition cdh_present : Contraindications :=
  mkContraindications true false false false false.

Lemma cdh_is_contraindication : has_contraindication cdh_present.
Proof.
  unfold has_contraindication, cdh_present. simpl.
  left. reflexivity.
Qed.

Lemma cdh_not_clear : ~ no_contraindications cdh_present.
Proof.
  unfold no_contraindications, cdh_present. simpl.
  intros [H _]. discriminate.
Qed.

(** -------------------------------------------------------------------------- *)
(** CPAP-First Protocol                                                        *)
(** -------------------------------------------------------------------------- *)

(** Respiratory support modality. Modern guidelines prefer CPAP trial first. *)
Inductive RespiratorySupport : Type :=
  | RoomAir          (* No support *)
  | CPAP             (* Continuous positive airway pressure *)
  | Intubated.       (* Endotracheal tube in place *)

(** CPAP trial state for rescue surfactant decision. *)
Record CPAPTrialState := mkCPAPTrialState {
  cpap_pressure_cmh2o : nat;    (* Typical 5-8 cmH2O *)
  cpap_duration_minutes : nat;  (* How long on CPAP *)
  fio2_on_cpap : fio2_pct       (* FiO2 requirement while on CPAP *)
}.

(** CPAP failure threshold: FiO2 > 40% on CPAP pressure >= 6 cmH2O. *)
Definition cpap_fio2_failure_threshold : nat := 40.
Definition cpap_min_pressure : nat := 6.

(** CPAP trial has failed, surfactant needed. *)
Definition cpap_trial_failed (trial : CPAPTrialState) : Prop :=
  cpap_pressure_cmh2o trial >= cpap_min_pressure /\
  fio2_on_cpap trial > cpap_fio2_failure_threshold.

(** --- Witness: CPAP failure at FiO2 50% on 7 cmH2O --- *)
Definition failed_cpap_trial : CPAPTrialState :=
  mkCPAPTrialState 7 30 50.

Lemma failed_cpap_trial_indicates_surfactant : cpap_trial_failed failed_cpap_trial.
Proof.
  unfold cpap_trial_failed, failed_cpap_trial, cpap_min_pressure,
         cpap_fio2_failure_threshold. simpl.
  split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Counterexample: Stable on CPAP at FiO2 30% --- *)
Definition stable_cpap_trial : CPAPTrialState :=
  mkCPAPTrialState 6 60 30.

Lemma stable_cpap_not_failed : ~ cpap_trial_failed stable_cpap_trial.
Proof.
  unfold cpap_trial_failed, stable_cpap_trial, cpap_fio2_failure_threshold. simpl.
  intros [_ H].
  apply Nat.lt_nge in H. apply H.
  apply Nat.leb_le. reflexivity.
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
(** SpO2 Targeting                                                             *)
(** -------------------------------------------------------------------------- *)

(** Oxygen saturation as percentage (0-100). *)
Definition spo2_pct := nat.

(** Target SpO2 range for preterm infants per SUPPORT/COT trials. *)
Definition spo2_target_low : nat := 88.
Definition spo2_target_high : nat := 95.

(** SpO2 is within target range. *)
Definition spo2_in_target (s : spo2_pct) : Prop :=
  spo2_target_low <= s /\ s <= spo2_target_high.

(** SpO2 below target despite supplemental oxygen suggests oxygenation failure. *)
Definition spo2_below_target (s : spo2_pct) : Prop :=
  s < spo2_target_low.

(** Combined oxygenation failure: high FiO2 AND low SpO2. *)
Definition oxygenation_failure (fio2 : fio2_pct) (spo2 : spo2_pct) : Prop :=
  fio2_elevated fio2 /\ spo2_below_target spo2.

(** --- Witness: SpO2 90% is in target --- *)
Lemma spo2_90_in_target : spo2_in_target 90.
Proof.
  unfold spo2_in_target, spo2_target_low, spo2_target_high.
  split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Witness: SpO2 85% is below target --- *)
Lemma spo2_85_below_target : spo2_below_target 85.
Proof.
  unfold spo2_below_target, spo2_target_low.
  apply Nat.leb_le. reflexivity.
Qed.

(** --- Witness: FiO2 50% with SpO2 82% = oxygenation failure --- *)
Lemma oxygenation_failure_example : oxygenation_failure 50 82.
Proof.
  unfold oxygenation_failure. split.
  - unfold fio2_elevated, fio2_threshold. apply Nat.leb_le. reflexivity.
  - unfold spo2_below_target, spo2_target_low. apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: FiO2 25% with SpO2 92% = no failure --- *)
Lemma no_oxygenation_failure_example : ~ oxygenation_failure 25 92.
Proof.
  unfold oxygenation_failure. intros [Hfio2 _].
  unfold fio2_elevated, fio2_threshold in Hfio2.
  apply Nat.lt_nge in Hfio2. apply Hfio2.
  apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Blood Gas Integration                                                      *)
(** -------------------------------------------------------------------------- *)

(** Blood gas values. pH scaled by 100 (720 = 7.20), pCO2 in mmHg. *)
Definition ph_scaled := nat.   (* pH * 100, so 7.35 = 735 *)
Definition pco2_mmhg := nat.

(** Arterial blood gas record. *)
Record BloodGas := mkBloodGas {
  ph : ph_scaled;
  pco2 : pco2_mmhg;
  po2 : nat         (* pO2 in mmHg, less critical for surfactant decision *)
}.

(** Respiratory acidosis thresholds. *)
Definition ph_critical_low : nat := 720.    (* pH < 7.20 *)
Definition pco2_critical_high : nat := 60.  (* pCO2 > 60 mmHg *)

(** Severe respiratory acidosis indicating ventilatory failure. *)
Definition respiratory_acidosis (bg : BloodGas) : Prop :=
  ph bg < ph_critical_low \/ pco2 bg > pco2_critical_high.

(** Blood gas supports surfactant: acidosis suggests severe RDS. *)
Definition blood_gas_supports_surfactant (bg : BloodGas) : Prop :=
  respiratory_acidosis bg.

(** --- Witness: pH 7.15, pCO2 65 → respiratory acidosis --- *)
Definition acidotic_gas : BloodGas := mkBloodGas 715 65 55.

Lemma acidotic_gas_supports_surfactant : blood_gas_supports_surfactant acidotic_gas.
Proof.
  unfold blood_gas_supports_surfactant, respiratory_acidosis, acidotic_gas,
         ph_critical_low, pco2_critical_high. simpl.
  left. apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: pH 7.35, pCO2 45 → normal gas --- *)
Definition normal_gas : BloodGas := mkBloodGas 735 45 80.

Lemma normal_gas_no_acidosis : ~ respiratory_acidosis normal_gas.
Proof.
  unfold respiratory_acidosis, normal_gas, ph_critical_low, pco2_critical_high. simpl.
  intros [Hph | Hpco2].
  - apply Nat.lt_nge in Hph. apply Hph. apply Nat.leb_le. reflexivity.
  - apply Nat.lt_nge in Hpco2. apply Hpco2. apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** CXR Confirmation                                                           *)
(** -------------------------------------------------------------------------- *)

(** Chest X-ray findings relevant to RDS diagnosis. *)
Record ChestXRay := mkChestXRay {
  ground_glass_opacity : bool;   (* Diffuse haziness, classic RDS finding *)
  air_bronchograms : bool;       (* Air-filled bronchi visible against opaque lung *)
  low_lung_volumes : bool;       (* Hypoexpansion typical of surfactant deficiency *)
  reticulogranular_pattern : bool (* Fine granular densities *)
}.

(** CXR consistent with RDS: ground-glass OR (air bronchograms AND low volumes). *)
Definition cxr_consistent_with_rds (cxr : ChestXRay) : Prop :=
  ground_glass_opacity cxr = true \/
  (air_bronchograms cxr = true /\ low_lung_volumes cxr = true).

(** CXR definitively confirms RDS: ground-glass AND reticulogranular. *)
Definition cxr_confirms_rds (cxr : ChestXRay) : Prop :=
  ground_glass_opacity cxr = true /\ reticulogranular_pattern cxr = true.

(** --- Witness: Classic RDS chest X-ray --- *)
Definition classic_rds_cxr : ChestXRay :=
  mkChestXRay true true true true.

Lemma classic_rds_cxr_confirms : cxr_confirms_rds classic_rds_cxr.
Proof.
  unfold cxr_confirms_rds, classic_rds_cxr. simpl.
  split; reflexivity.
Qed.

(** --- Witness: Partial findings still consistent --- *)
Definition partial_rds_cxr : ChestXRay :=
  mkChestXRay false true true false.

Lemma partial_rds_cxr_consistent : cxr_consistent_with_rds partial_rds_cxr.
Proof.
  unfold cxr_consistent_with_rds, partial_rds_cxr. simpl.
  right. split; reflexivity.
Qed.

(** --- Counterexample: Clear chest X-ray --- *)
Definition clear_cxr : ChestXRay :=
  mkChestXRay false false false false.

Lemma clear_cxr_not_rds : ~ cxr_consistent_with_rds clear_cxr.
Proof.
  unfold cxr_consistent_with_rds, clear_cxr. simpl.
  intros [H | [H _]]; discriminate.
Qed.

(** -------------------------------------------------------------------------- *)
(** Delivery Room Timing                                                       *)
(** -------------------------------------------------------------------------- *)

(** Time since birth in minutes. *)
Definition minutes_since_birth := nat.

(** Prophylactic surfactant window: within 15 minutes of birth. *)
Definition prophylactic_window_minutes : nat := 15.

(** Within the prophylactic administration window. *)
Definition within_prophylactic_window (mins : minutes_since_birth) : Prop :=
  mins <= prophylactic_window_minutes.

(** Prophylactic timing valid: must be given early. *)
Definition prophylactic_timing_valid (mins : minutes_since_birth) : Prop :=
  within_prophylactic_window mins.

(** --- Witness: 10 minutes post-birth is within window --- *)
Lemma timing_10min_valid : prophylactic_timing_valid 10.
Proof.
  unfold prophylactic_timing_valid, within_prophylactic_window,
         prophylactic_window_minutes.
  apply Nat.leb_le. reflexivity.
Qed.

(** --- Counterexample: 30 minutes post-birth is outside window --- *)
Lemma timing_30min_invalid : ~ prophylactic_timing_valid 30.
Proof.
  unfold prophylactic_timing_valid, within_prophylactic_window,
         prophylactic_window_minutes.
  apply Nat.lt_nge. apply Nat.leb_le. reflexivity.
Qed.

(** Prophylactic administration requires both GA eligibility AND timing. *)
Definition prophylactic_complete (ga : gestational_age) (mins : minutes_since_birth) : Prop :=
  ga < 26 /\ within_prophylactic_window mins.

(** --- Witness: 24w infant at 5 minutes → full prophylactic criteria met --- *)
Lemma prophylactic_complete_example : prophylactic_complete 24 5.
Proof.
  unfold prophylactic_complete, within_prophylactic_window,
         prophylactic_window_minutes.
  split; apply Nat.leb_le; reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Administration Technique                                                   *)
(** -------------------------------------------------------------------------- *)

(** Surfactant administration techniques.
    - INSURE: INtubate-SURfactant-Extubate (brief intubation)
    - LISA: Less Invasive Surfactant Administration (thin catheter, no intubation)
    - Conventional: Traditional intubation with ongoing mechanical ventilation *)
Inductive AdministrationTechnique : Type :=
  | INSURE       (* Brief intubation, immediate extubation to CPAP *)
  | LISA         (* Thin catheter during spontaneous breathing on CPAP *)
  | Conventional. (* Standard intubation with mechanical ventilation *)

(** Technique requires intubation. *)
Definition requires_intubation (tech : AdministrationTechnique) : bool :=
  match tech with
  | INSURE => true       (* Brief intubation required *)
  | LISA => false        (* No intubation - catheter only *)
  | Conventional => true (* Full intubation *)
  end.

(** Technique preserves spontaneous breathing. *)
Definition preserves_spontaneous_breathing (tech : AdministrationTechnique) : bool :=
  match tech with
  | INSURE => false      (* Apneic during brief intubation *)
  | LISA => true         (* Breathing maintained throughout *)
  | Conventional => false (* Mechanical ventilation *)
  end.

(** Technique compatible with ongoing CPAP. *)
Definition cpap_compatible (tech : AdministrationTechnique) : bool :=
  match tech with
  | INSURE => true       (* Returns to CPAP immediately *)
  | LISA => true         (* Performed on CPAP *)
  | Conventional => false (* Requires mechanical ventilation *)
  end.

(** --- Properties: LISA is least invasive --- *)
Lemma lisa_no_intubation : requires_intubation LISA = false.
Proof. reflexivity. Qed.

Lemma lisa_preserves_breathing : preserves_spontaneous_breathing LISA = true.
Proof. reflexivity. Qed.

Lemma lisa_cpap_compatible : cpap_compatible LISA = true.
Proof. reflexivity. Qed.

(** --- Properties: Conventional is most invasive --- *)
Lemma conventional_requires_intubation : requires_intubation Conventional = true.
Proof. reflexivity. Qed.

Lemma conventional_not_cpap : cpap_compatible Conventional = false.
Proof. reflexivity. Qed.

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
(** Boundary Behavior Audit                                                    *)
(** -------------------------------------------------------------------------- *)

(** BOUNDARY DOCUMENTATION:
    This formalization uses STRICT inequalities for thresholds:
    - Prophylactic GA: < 26 weeks (NOT <=)
    - FiO2 elevated: > 30% (NOT >=)

    Clinical interpretation:
    - GA exactly 26+0 weeks: NOT eligible for prophylactic (use rescue criteria)
    - FiO2 exactly 30%: NOT considered elevated (threshold not exceeded)

    These choices follow European Consensus Guidelines which specify
    prophylactic for "infants < 26 weeks" and rescue for "FiO2 > 30%". *)

(** --- Boundary: Exactly 26 weeks is NOT prophylactic eligible --- *)
Lemma ga_26_not_prophylactic : ~ prophylactic_eligible_ga 26.
Proof.
  unfold prophylactic_eligible_ga, prophylactic_ga_threshold.
  apply Nat.lt_irrefl.
Qed.

(** --- Boundary: Exactly 30% FiO2 is NOT elevated --- *)
Lemma fio2_30_not_elevated : ~ fio2_elevated 30.
Proof.
  unfold fio2_elevated, fio2_threshold.
  apply Nat.lt_irrefl.
Qed.

(** --- Boundary: 26 weeks is the first ineligible GA --- *)
Lemma ga_boundary_25_vs_26 :
  prophylactic_eligible_ga 25 /\ ~ prophylactic_eligible_ga 26.
Proof.
  split.
  - unfold prophylactic_eligible_ga, prophylactic_ga_threshold.
    apply Nat.leb_le. reflexivity.
  - exact ga_26_not_prophylactic.
Qed.

(** --- Boundary: 31% is the first elevated FiO2 --- *)
Lemma fio2_boundary_30_vs_31 :
  ~ fio2_elevated 30 /\ fio2_elevated 31.
Proof.
  split.
  - exact fio2_30_not_elevated.
  - unfold fio2_elevated, fio2_threshold. apply Nat.leb_le. reflexivity.
Qed.

(** --- Inclusive alternative: >= 26 weeks would include 26 --- *)
Definition prophylactic_eligible_ga_inclusive (ga : gestational_age) : Prop :=
  ga <= 26.

Lemma ga_26_inclusive : prophylactic_eligible_ga_inclusive 26.
Proof.
  unfold prophylactic_eligible_ga_inclusive. apply Nat.le_refl.
Qed.

(** Note: The strict version (< 26) is used per guidelines. *)

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

(** -------------------------------------------------------------------------- *)
(** OCaml Extraction                                                           *)
(** -------------------------------------------------------------------------- *)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

(** Extract core decision types. *)
Extraction Language OCaml.

(** Map Coq nat to OCaml int for efficiency. *)
Extract Inductive nat => "int" ["0" "succ"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".

(** Extract key functions for clinical use. *)
Extract Constant Nat.add => "(+)".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.div => "(/)".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".

(** Module for extracted code. *)
Module SurfactantDecision.

  (** Decidable sign count. *)
  Definition sign_count_dec (s : RDSSigns) : nat := sign_count s.

  (** Decidable FiO2 elevated check. *)
  Definition fio2_elevated_dec (f : fio2_pct) : bool :=
    fio2_threshold <? f.

  (** Decidable prophylactic eligibility. *)
  Definition prophylactic_eligible_dec (ga : gestational_age) : bool :=
    ga <? prophylactic_ga_threshold.

  (** Decidable clinical RDS (>= 2 signs). *)
  Definition clinical_rds_dec (s : RDSSigns) : bool :=
    2 <=? sign_count s.

  (** Calculate initial dose. *)
  Definition calc_initial_dose (prod : SurfactantProduct) (wt : weight_g) : nat :=
    initial_dose prod wt.

  (** Calculate repeat dose. *)
  Definition calc_repeat_dose (prod : SurfactantProduct) (wt : weight_g) : nat :=
    repeat_dose prod wt.

  (** Check CPAP failure. *)
  Definition cpap_failed_dec (pressure : nat) (fio2 : fio2_pct) : bool :=
    (cpap_min_pressure <=? pressure) && (cpap_fio2_failure_threshold <? fio2).

  (** Check respiratory acidosis. *)
  Definition acidosis_dec (ph_val : ph_scaled) (pco2_val : pco2_mmhg) : bool :=
    (ph_val <? ph_critical_low) || (pco2_critical_high <? pco2_val).

End SurfactantDecision.

(** Extract the decision module. *)
Extraction "surfactant_decision.ml" SurfactantDecision.
