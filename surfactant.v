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

(** -------------------------------------------------------------------------- *)
(** TODO                                                                        *)
(** -------------------------------------------------------------------------- *)

(**
   [DONE] 1. SF ratio: 264 ≈ P/F 300 (mild ARDS). See sf_threshold comment.

   [DONE] 2. OI thresholds: ECMO > 40, transfer > 25. See oxygenation_index comment.

   [DONE] 3. max_single_dose: documented as weight-range modeling assumptions.

   [DONE] 4. rescue_recommendation: proved conservative vs guideline-minimal.
             See conservative_implies_guideline, conservative_rejects_case.

   [DONE] 5. OCaml extraction safety: validate_clinical_state checks all fields,
             recommend_surfactant_safe returns InvalidInput on range errors.
*)

From Coq Require Import Arith Lia.

(** -------------------------------------------------------------------------- *)
(** Patient Record                                                             *)
(** -------------------------------------------------------------------------- *)

(** Gestational age in completed weeks (22-42 typical range). *)
Definition gestational_age := nat.

(** Gestational age days component (0-6). *)
Definition ga_days_t := nat.

(** Birth weight in grams. *)
Definition weight_g := nat.

(** Postnatal age in hours. *)
Definition postnatal_hours := nat.

(** FiO2 as percentage (21-100). 21 = room air, 100 = pure oxygen. *)
Definition fio2_pct := nat.

(** Patient state for surfactant decision. GA expressed as weeks+days: 29+6 → 29, 6. *)
Record Patient := mkPatient {
  ga_weeks : gestational_age;
  ga_days : ga_days_t;
  birth_weight : weight_g;
  age_hours : postnatal_hours;
  current_fio2 : fio2_pct
}.

(** Total gestational age in days. *)
Definition ga_total_days (p : Patient) : nat :=
  ga_weeks p * 7 + ga_days p.

(** Validity predicate: GA and weight within physiological bounds. *)
Definition valid_patient (p : Patient) : Prop :=
  22 <= ga_weeks p /\ ga_weeks p <= 42 /\
  ga_days p <= 6 /\
  200 <= birth_weight p /\ birth_weight p <= 6000 /\
  21 <= current_fio2 p /\ current_fio2 p <= 100.

(** --- Witness: A valid 26+0 week, 800g infant --- *)
Definition witness_patient : Patient :=
  mkPatient 26 0 800 2 45.

Lemma witness_patient_valid : valid_patient witness_patient.
Proof.
  unfold valid_patient, witness_patient. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Counterexample: Invalid GA (50 weeks) --- *)
Definition invalid_patient_ga : Patient :=
  mkPatient 50 0 3000 1 21.

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
  unfold clinical_rds, sign_count, witness_rds_signs. simpl. lia.
Qed.

(** --- Counterexample: Infant with 0 signs --- *)
Definition no_rds_signs : RDSSigns :=
  mkRDSSigns false false false false.

Lemma no_rds_signs_negative : ~ clinical_rds no_rds_signs.
Proof.
  unfold clinical_rds, sign_count, no_rds_signs. simpl. lia.
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

(** CPAP failure threshold per European Consensus 2022:
    FiO2 > 30% on CPAP pressure >= 6 cmH2O indicates surfactant needed. *)
Definition cpap_fio2_failure_threshold : nat := 30.
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
         cpap_fio2_failure_threshold. simpl. lia.
Qed.

(** --- Counterexample: Stable on CPAP at FiO2 30% --- *)
Definition stable_cpap_trial : CPAPTrialState :=
  mkCPAPTrialState 6 60 30.

Lemma stable_cpap_not_failed : ~ cpap_trial_failed stable_cpap_trial.
Proof.
  unfold cpap_trial_failed, stable_cpap_trial, cpap_fio2_failure_threshold,
         cpap_min_pressure. simpl. lia.
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
  unfold fio2_elevated, fio2_threshold. lia.
Qed.

(** --- Counterexample: FiO2 25% does not exceed threshold --- *)
Lemma fio2_25_not_elevated : ~ fio2_elevated 25.
Proof.
  unfold fio2_elevated, fio2_threshold. lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** SpO2 Targeting                                                             *)
(** -------------------------------------------------------------------------- *)

(** Oxygen saturation as percentage (0-100). *)
Definition spo2_pct := nat.

(** Target SpO2 range for preterm infants per European Consensus 2022.
    Target 90-94% with alarm limits at 89% and 95%. *)
Definition spo2_target_low : nat := 90.
Definition spo2_target_high : nat := 94.

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
  unfold spo2_below_target, spo2_target_low. lia.
Qed.

(** --- Witness: FiO2 50% with SpO2 82% = oxygenation failure --- *)
Lemma oxygenation_failure_example : oxygenation_failure 50 82.
Proof.
  unfold oxygenation_failure, fio2_elevated, fio2_threshold,
         spo2_below_target, spo2_target_low. lia.
Qed.

(** --- Counterexample: FiO2 25% with SpO2 92% = no failure --- *)
Lemma no_oxygenation_failure_example : ~ oxygenation_failure 25 92.
Proof.
  unfold oxygenation_failure, fio2_elevated, fio2_threshold. lia.
Qed.

(** SpO2/FiO2 ratio (SF ratio) as oxygenation metric.
    SF ratio approximates PaO2/FiO2 (P/F ratio) noninvasively.
    Per Rice 2007: SF ~235 ≈ P/F 200, SF ~264 ≈ P/F 300.
    SF < 264 thus approximates P/F < 300 (mild ARDS boundary).
    NOTE: SF ratio is an adjunct research metric, not part of
    European 2022 RDS surfactant guidelines.
    Calculated as SpO2 * 100 / FiO2 to preserve integer arithmetic. *)
Definition sf_ratio (spo2 : spo2_pct) (fio2 : fio2_pct) : nat :=
  spo2 * 100 / fio2.

(** SF ratio threshold: 264 ≈ P/F 300 (mild ARDS/hypoxemia boundary).
    For moderate ARDS (P/F < 200), use threshold ~235. *)
Definition sf_threshold : nat := 264.

(** SF ratio below threshold suggests surfactant need. *)
Definition sf_impaired (spo2 : spo2_pct) (fio2 : fio2_pct) : Prop :=
  sf_ratio spo2 fio2 < sf_threshold.

(** --- Witness: SpO2 88% on FiO2 50% → SF 176 (impaired) --- *)
Lemma sf_impaired_example : sf_impaired 88 50.
Proof.
  unfold sf_impaired, sf_ratio, sf_threshold. simpl. lia.
Qed.

(** --- Counterexample: SpO2 92% on FiO2 30% → SF 306 (adequate) --- *)
Lemma sf_adequate_example : ~ sf_impaired 92 30.
Proof.
  unfold sf_impaired, sf_ratio, sf_threshold. simpl. lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** Blood Gas Integration                                                      *)
(** -------------------------------------------------------------------------- *)

(** Blood gas values. pH scaled by 1000 (7200 = 7.20), pCO2 in mmHg. *)
Definition ph_scaled := nat.   (* pH * 1000, so 7.35 = 7350 *)
Definition pco2_mmhg := nat.

(** Arterial blood gas record. *)
Record BloodGas := mkBloodGas {
  ph : ph_scaled;
  pco2 : pco2_mmhg;
  po2 : nat         (* pO2 in mmHg, less critical for surfactant decision *)
}.

(** Respiratory acidosis thresholds. *)
Definition ph_critical_low : nat := 7200.   (* pH < 7.20 *)
Definition pco2_critical_high : nat := 60.  (* pCO2 > 60 mmHg *)

(** Severe respiratory acidosis indicating ventilatory failure. *)
Definition respiratory_acidosis (bg : BloodGas) : Prop :=
  ph bg < ph_critical_low \/ pco2 bg > pco2_critical_high.

(** Blood gas supports surfactant: acidosis suggests severe RDS. *)
Definition blood_gas_supports_surfactant (bg : BloodGas) : Prop :=
  respiratory_acidosis bg.

(** --- Witness: pH 7.15, pCO2 65 → respiratory acidosis --- *)
Definition acidotic_gas : BloodGas := mkBloodGas 7150 65 55.

Lemma acidotic_gas_supports_surfactant : blood_gas_supports_surfactant acidotic_gas.
Proof.
  unfold blood_gas_supports_surfactant, respiratory_acidosis, acidotic_gas,
         ph_critical_low, pco2_critical_high. simpl. left.
  apply Nat.ltb_lt. reflexivity.
Qed.

(** --- Counterexample: pH 7.35, pCO2 45 → normal gas --- *)
Definition normal_gas : BloodGas := mkBloodGas 7350 45 80.

Lemma normal_gas_no_acidosis : ~ respiratory_acidosis normal_gas.
Proof.
  unfold respiratory_acidosis, normal_gas, ph_critical_low, pco2_critical_high.
  simpl. intros [H | H]; apply Nat.ltb_ge in H; discriminate.
Qed.

(** Mean airway pressure in cmH2O. *)
Definition map_cmh2o := nat.

(** Oxygenation index: OI = (FiO2 × MAP) / PaO2.
    Since FiO2 is already percentage (not fraction), no ×100 needed.
    Integrates oxygen requirement with ventilator support intensity.
    Thresholds (population-dependent):
    - OI > 15-16: severe hypoxemia (PARDS criteria)
    - OI > 25: consider transfer to ECMO-capable center
    - OI > 40: typical neonatal ECMO initiation threshold
    NOTE: OI is an adjunct severity metric, not part of European 2022
    RDS surfactant guidelines. *)
Definition oxygenation_index (fio2 : fio2_pct) (map : map_cmh2o) (pao2 : nat) : nat :=
  fio2 * map / pao2.

(** OI thresholds for severity classification.
    oi_severe: PARDS severe threshold (~16)
    oi_critical: transfer/consult threshold (not ECMO initiation) *)
Definition oi_severe : nat := 15.
Definition oi_critical : nat := 25.

(** Severe oxygenation failure by OI. *)
Definition oi_indicates_severe (fio2 : fio2_pct) (map : map_cmh2o) (pao2 : nat) : Prop :=
  oxygenation_index fio2 map pao2 > oi_severe.

(** --- Witness: FiO2 60%, MAP 12, PaO2 45 → OI 16 (severe) --- *)
Lemma oi_severe_example : oi_indicates_severe 60 12 45.
Proof.
  unfold oi_indicates_severe, oxygenation_index, oi_severe. simpl. lia.
Qed.

(** --- Counterexample: FiO2 40%, MAP 8, PaO2 70 → OI 4 (not severe) --- *)
Lemma oi_not_severe_example : ~ oi_indicates_severe 40 8 70.
Proof.
  unfold oi_indicates_severe, oxygenation_index, oi_severe. simpl. lia.
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

(** Lung ultrasound findings per European Consensus 2022.
    Ultrasound is increasingly used as alternative to CXR. *)
Record LungUltrasound := mkLungUltrasound {
  bilateral_white_lung : bool;       (* Confluent B-lines, "white lung" *)
  absent_a_lines : bool;             (* Loss of normal pleural lines *)
  pleural_irregularity : bool;       (* Thickened/irregular pleura *)
  consolidations : bool              (* Subpleural consolidations *)
}.

(** Ultrasound consistent with RDS: white lung OR consolidations with pleural changes. *)
Definition ultrasound_consistent_with_rds (us : LungUltrasound) : Prop :=
  bilateral_white_lung us = true \/
  (consolidations us = true /\ pleural_irregularity us = true).

(** --- Witness: Classic RDS ultrasound --- *)
Definition rds_ultrasound : LungUltrasound :=
  mkLungUltrasound true true true false.

Lemma rds_ultrasound_consistent : ultrasound_consistent_with_rds rds_ultrasound.
Proof.
  unfold ultrasound_consistent_with_rds, rds_ultrasound. simpl.
  left. reflexivity.
Qed.

(** Imaging evidence for RDS: CXR OR ultrasound OR clinical judgement.
    Per European Consensus 2022, imaging is supportive but not required
    when clinical presentation is clear. *)
Record ImagingEvidence := mkImagingEvidence {
  ie_cxr : option ChestXRay;
  ie_ultrasound : option LungUltrasound;
  ie_clinical_judgement : bool  (* Experienced clinician diagnosis without imaging *)
}.

(** Imaging supports RDS diagnosis. *)
Definition imaging_supports_rds (ie : ImagingEvidence) : Prop :=
  match ie_cxr ie with
  | Some cxr => cxr_consistent_with_rds cxr
  | None => False
  end \/
  match ie_ultrasound ie with
  | Some us => ultrasound_consistent_with_rds us
  | None => False
  end \/
  ie_clinical_judgement ie = true.

(** --- Witness: CXR-based evidence --- *)
Definition cxr_evidence : ImagingEvidence :=
  mkImagingEvidence (Some classic_rds_cxr) None false.

Lemma cxr_evidence_supports : imaging_supports_rds cxr_evidence.
Proof.
  unfold imaging_supports_rds, cxr_evidence. simpl.
  left. unfold cxr_consistent_with_rds, classic_rds_cxr. simpl.
  left. reflexivity.
Qed.

(** --- Witness: Clinical judgement alone --- *)
Definition clinical_evidence : ImagingEvidence :=
  mkImagingEvidence None None true.

Lemma clinical_evidence_supports : imaging_supports_rds clinical_evidence.
Proof.
  unfold imaging_supports_rds, clinical_evidence. simpl.
  right. right. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Delivery Room Timing                                                       *)
(** -------------------------------------------------------------------------- *)

(** Time since birth in minutes. *)
Definition minutes_since_birth := nat.

(** Prophylactic surfactant window (conservative default): within 15 minutes.
    Product-specific timing: Survanta 15 min, Infasurf 30 min.
    See prophylactic_window_for_product for product-specific version. *)
Definition prophylactic_window_minutes : nat := 15.

(** Within the prophylactic administration window. *)
Definition within_prophylactic_window (mins : minutes_since_birth) : Prop :=
  mins <= prophylactic_window_minutes.

(** --- Witness: 10 minutes post-birth is within window --- *)
Lemma timing_10min_valid : within_prophylactic_window 10.
Proof.
  unfold within_prophylactic_window, prophylactic_window_minutes. lia.
Qed.

(** --- Counterexample: 20 minutes post-birth exceeds conservative window --- *)
Lemma timing_20min_invalid : ~ within_prophylactic_window 20.
Proof.
  unfold within_prophylactic_window, prophylactic_window_minutes. lia.
Qed.

(** Prophylactic administration requires GA eligibility, timing, AND intubation.
    GA threshold is 30 weeks per European Consensus 2022. *)
Definition prophylactic_complete (ga : gestational_age) (mins : minutes_since_birth)
                                 (support : RespiratorySupport) : Prop :=
  ga < 30 /\
  within_prophylactic_window mins /\
  support = Intubated.

(** --- Witness: 28w infant at 5 minutes, intubated → prophylactic criteria met --- *)
Lemma prophylactic_complete_example : prophylactic_complete 28 5 Intubated.
Proof.
  unfold prophylactic_complete, within_prophylactic_window,
         prophylactic_window_minutes. simpl.
  repeat split; try lia; try reflexivity.
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

(** LISA eligibility requirements:
    1. Spontaneous breathing (not apneic)
    2. GA >= 25 weeks (safer threshold for thin catheter)
    3. Currently on CPAP (not intubated or room air) *)
Definition lisa_ga_threshold : nat := 25.

Definition lisa_eligible (ga : gestational_age) (support : RespiratorySupport)
                         (breathing_spontaneously : bool) : Prop :=
  ga >= lisa_ga_threshold /\
  support = CPAP /\
  breathing_spontaneously = true.

(** --- Witness: 28w infant on CPAP, breathing → LISA eligible --- *)
Lemma lisa_eligible_example : lisa_eligible 28 CPAP true.
Proof.
  unfold lisa_eligible, lisa_ga_threshold.
  repeat split; try lia; try reflexivity.
Qed.

(** --- Counterexample: 24w infant too young for LISA --- *)
Lemma lisa_24w_not_eligible : ~ lisa_eligible 24 CPAP true.
Proof.
  unfold lisa_eligible, lisa_ga_threshold. intros [Hga _]. lia.
Qed.

(** --- Counterexample: Intubated infant cannot receive LISA --- *)
Lemma lisa_intubated_not_eligible : ~ lisa_eligible 28 Intubated true.
Proof.
  unfold lisa_eligible. intros [_ [Hsup _]]. discriminate.
Qed.

(** --- Counterexample: Apneic infant cannot receive LISA --- *)
Lemma lisa_apneic_not_eligible : ~ lisa_eligible 28 CPAP false.
Proof.
  unfold lisa_eligible. intros [_ [_ Hbreath]]. discriminate.
Qed.

(** --- Properties: Conventional is most invasive --- *)
Lemma conventional_requires_intubation : requires_intubation Conventional = true.
Proof. reflexivity. Qed.

Lemma conventional_not_cpap : cpap_compatible Conventional = false.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Gestational Age Thresholds                                                 *)
(** -------------------------------------------------------------------------- *)

(** Prophylactic surfactant threshold: < 30 weeks per European Consensus 2022.
    Guideline: preterm infant <30 weeks requiring intubation for stabilization. *)
Definition prophylactic_ga_threshold : nat := 30.

(** Eligible for prophylactic surfactant based on GA alone. *)
Definition prophylactic_eligible_ga (ga : gestational_age) : Prop :=
  ga < prophylactic_ga_threshold.

(** --- Witness: 25 weeks eligible for prophylactic --- *)
Lemma ga_25_prophylactic_eligible : prophylactic_eligible_ga 25.
Proof.
  unfold prophylactic_eligible_ga, prophylactic_ga_threshold. lia.
Qed.

(** --- Counterexample: 32 weeks not eligible for prophylactic --- *)
Lemma ga_32_not_prophylactic_eligible : ~ prophylactic_eligible_ga 32.
Proof.
  unfold prophylactic_eligible_ga, prophylactic_ga_threshold. lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** Boundary Behavior Audit                                                    *)
(** -------------------------------------------------------------------------- *)

(** BOUNDARY DOCUMENTATION:
    This formalization uses STRICT inequalities for thresholds:
    - Prophylactic GA: < 30 weeks (NOT <=)
    - FiO2 elevated: > 30% (NOT >=)

    Clinical interpretation:
    - GA exactly 30+0 weeks: NOT eligible for prophylactic (use rescue criteria)
    - FiO2 exactly 30%: NOT considered elevated (threshold not exceeded)

    These choices follow European Consensus Guidelines 2022 which specify
    prophylactic for "infants < 30 weeks requiring intubation" and
    rescue for "FiO2 > 30%". *)

(** --- Boundary: Exactly 30 weeks is NOT prophylactic eligible (by GA) --- *)
Lemma ga_30_not_prophylactic : ~ prophylactic_eligible_ga 30.
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

(** --- Boundary: 30 weeks is the first ineligible GA --- *)
Lemma ga_boundary_29_vs_30 :
  prophylactic_eligible_ga 29 /\ ~ prophylactic_eligible_ga 30.
Proof.
  split.
  - unfold prophylactic_eligible_ga, prophylactic_ga_threshold. lia.
  - exact ga_30_not_prophylactic.
Qed.

(** --- Boundary: 31% is the first elevated FiO2 --- *)
Lemma fio2_boundary_30_vs_31 :
  ~ fio2_elevated 30 /\ fio2_elevated 31.
Proof.
  split.
  - exact fio2_30_not_elevated.
  - unfold fio2_elevated, fio2_threshold. lia.
Qed.

(** --- Inclusive alternative: <= 30 weeks would include 30 --- *)
Definition prophylactic_eligible_ga_inclusive (ga : gestational_age) : Prop :=
  ga <= 30.

Lemma ga_30_inclusive : prophylactic_eligible_ga_inclusive 30.
Proof.
  unfold prophylactic_eligible_ga_inclusive. apply Nat.le_refl.
Qed.

(** Note: The strict version (< 30) is used per guidelines. *)

(** -------------------------------------------------------------------------- *)
(** Indication Logic (Core Criteria)                                           *)
(** -------------------------------------------------------------------------- *)

(** NOTE: These predicates capture the CORE indication criteria only.
    For complete clinical decision-making, use surfactant_recommendation
    which integrates timing, contraindications, CXR, and CPAP context. *)

(** Prophylactic indication (core): GA < 30+0 weeks (< 210 days).
    Uses precise GA including days: 29+6 (209 days) qualifies, 30+0 (210) doesn't. *)
Definition prophylactic_indicated (p : Patient) : Prop :=
  ga_total_days p < 210.

(** Rescue indication (core): FiO2 elevated AND clinical signs present.
    Full rescue recommendation also requires CXR consistency and CPAP context. *)
Definition rescue_indicated (p : Patient) (signs : RDSSigns) : Prop :=
  fio2_elevated (current_fio2 p) /\ clinical_rds signs.

(** Combined indication (core): prophylactic OR rescue.
    For clinical use, prefer surfactant_recommendation which enforces
    additional safety checks (contraindications, timing, CPAP trial). *)
Definition surfactant_indicated (p : Patient) (signs : RDSSigns) : Prop :=
  prophylactic_indicated p \/ rescue_indicated p signs.

(** --- Witness: 27w infant with FiO2 40% and signs → rescue indicated --- *)
Definition rescue_patient : Patient := mkPatient 27 0 900 6 40.
Definition rescue_signs : RDSSigns := mkRDSSigns true true false false.

Lemma rescue_patient_indicated : surfactant_indicated rescue_patient rescue_signs.
Proof.
  unfold surfactant_indicated. right.
  unfold rescue_indicated, fio2_elevated, fio2_threshold, rescue_patient,
         clinical_rds, sign_count, rescue_signs. simpl. lia.
Qed.

(** --- Counterexample: 34w infant with FiO2 21% and no signs → not indicated --- *)
Definition well_patient : Patient := mkPatient 34 0 2200 12 21.
Definition well_signs : RDSSigns := mkRDSSigns false false false false.

Lemma well_patient_not_indicated : ~ surfactant_indicated well_patient well_signs.
Proof.
  unfold surfactant_indicated, prophylactic_indicated, ga_total_days,
         rescue_indicated, fio2_elevated, fio2_threshold,
         well_patient. simpl. lia.
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

(** Product-specific prophylactic timing windows per FDA labeling. *)
Definition prophylactic_window_for_product (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 15  (* "preferably within 15 minutes of birth" *)
  | Curosurf => 15  (* European guidelines, not strict prophylaxis *)
  | Infasurf => 30  (* "within 30 minutes of birth" *)
  end.

(** Within prophylactic window for specific product. *)
Definition within_prophylactic_window_for (prod : SurfactantProduct)
                                          (mins : minutes_since_birth) : Prop :=
  mins <= prophylactic_window_for_product prod.

(** --- Witness: 25 min valid for Infasurf but not Survanta --- *)
Lemma timing_25min_infasurf_valid : within_prophylactic_window_for Infasurf 25.
Proof.
  unfold within_prophylactic_window_for, prophylactic_window_for_product.
  simpl. lia.
Qed.

Lemma timing_25min_survanta_invalid : ~ within_prophylactic_window_for Survanta 25.
Proof.
  unfold within_prophylactic_window_for, prophylactic_window_for_product.
  simpl. lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** Dose Calculation                                                           *)
(** -------------------------------------------------------------------------- *)

(** Calculate dose in mg: weight_g * dose_per_kg / 1000.
    Integer division truncates: 849g at 100mg/kg → 84mg. *)
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

(** Product-specific maximum single doses.
    NOTE: These are DERIVED MODELING ASSUMPTIONS for specific weight ranges,
    not direct label quotes. FDA labels specify mg/kg (weight-based), not
    absolute mg caps. Derivations:
    - Survanta: 100 mg/kg × 4 kg assumed max = 400 mg
    - Curosurf: 200 mg/kg × 3 kg assumed max = 600 mg
    - Infasurf: 105 mg/kg × 4 kg assumed max = 420 mg
    This formalization supports weights up to ~3-4 kg. For larger infants,
    these caps may be too restrictive; consult actual label for dose/kg. *)
Definition max_single_dose (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 400  (* 100 mg/kg × 4 kg *)
  | Curosurf => 600  (* 200 mg/kg × 3 kg *)
  | Infasurf => 420  (* 105 mg/kg × 4 kg *)
  end.

(** Product- and weight-aware dose validity.
    Dose must be positive and within product-specific maximum. *)
Definition dose_valid_for_product (prod : SurfactantProduct) (dose : nat) : Prop :=
  dose > 0 /\ dose <= max_single_dose prod.

(** Calculated dose validity: checks that calculated dose is within bounds. *)
Definition calculated_dose_valid (prod : SurfactantProduct) (weight : weight_g)
                                 (is_initial : bool) : Prop :=
  let dose := if is_initial then initial_dose prod weight
              else repeat_dose prod weight in
  dose_valid_for_product prod dose.

(** Legacy dose validity (conservative bound for any product). *)
Definition dose_valid (dose : nat) : Prop :=
  dose > 0 /\ dose <= 600.

(** --- Witness: 160mg valid for Curosurf --- *)
Lemma dose_160_valid_curosurf : dose_valid_for_product Curosurf 160.
Proof.
  unfold dose_valid_for_product, max_single_dose. lia.
Qed.

(** --- Witness: 400mg valid for Survanta (at max) --- *)
Lemma dose_400_valid_survanta : dose_valid_for_product Survanta 400.
Proof.
  unfold dose_valid_for_product, max_single_dose. lia.
Qed.

(** --- Counterexample: 500mg exceeds Survanta max --- *)
Lemma dose_500_invalid_survanta : ~ dose_valid_for_product Survanta 500.
Proof.
  unfold dose_valid_for_product, max_single_dose. lia.
Qed.

(** --- Counterexample: 700mg exceeds Curosurf max --- *)
Lemma dose_700_invalid_curosurf : ~ dose_valid_for_product Curosurf 700.
Proof.
  unfold dose_valid_for_product, max_single_dose. lia.
Qed.

(** Per-product dose bounds for clinically appropriate weight ranges. *)
Theorem initial_dose_bounded_survanta :
  forall weight, weight <= 4000 ->
    initial_dose Survanta weight <= 400.
Proof.
  intros weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  apply Nat.le_trans with (4000 * 100 / 1000).
  - apply Nat.Div0.div_le_mono. lia.
  - apply Nat.leb_le. reflexivity.
Qed.

Theorem initial_dose_bounded_curosurf :
  forall weight, weight <= 3000 ->
    initial_dose Curosurf weight <= 600.
Proof.
  intros weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  apply Nat.le_trans with (3000 * 200 / 1000).
  - apply Nat.Div0.div_le_mono. lia.
  - apply Nat.leb_le. reflexivity.
Qed.

Theorem initial_dose_bounded_infasurf :
  forall weight, weight <= 4000 ->
    initial_dose Infasurf weight <= 420.
Proof.
  intros weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  apply Nat.le_trans with (4000 * 105 / 1000).
  - apply Nat.Div0.div_le_mono. lia.
  - apply Nat.leb_le. reflexivity.
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

(** Minimum hours between doses per FDA product labeling.
    Survanta: "no more frequently than every 6 hours"
    Curosurf: "approximately 12-hour intervals"
    Infasurf: "every 12 hours" *)
Definition min_hours_between_doses (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 6
  | Curosurf => 12
  | Infasurf => 12
  end.

(** Eligible for repeat dose: under max AND enough time passed AND still needing O2. *)
Definition repeat_eligible (ds : DosingState) (current_fio2 : fio2_pct) : Prop :=
  doses_given ds < max_doses (product ds) /\
  hours_since_last ds >= min_hours_between_doses (product ds) /\
  fio2_elevated current_fio2.

(** --- Witness: 2nd dose of Survanta, 8 hours later, FiO2 40% → eligible --- *)
Definition eligible_repeat_state : DosingState := mkDosingState Survanta 1 8.

Lemma eligible_repeat_state_ok : repeat_eligible eligible_repeat_state 40.
Proof.
  unfold repeat_eligible, eligible_repeat_state, min_hours_between_doses,
         fio2_elevated, fio2_threshold. simpl. lia.
Qed.

(** --- Counterexample: 5th dose of Survanta (max 4) → not eligible --- *)
Definition max_doses_exceeded : DosingState := mkDosingState Survanta 4 12.

Lemma max_doses_exceeded_ineligible : ~ repeat_eligible max_doses_exceeded 40.
Proof.
  unfold repeat_eligible, max_doses_exceeded. simpl. lia.
Qed.

(** --- Counterexample: Too soon (3 hours, need 6) → not eligible --- *)
Definition too_soon_state : DosingState := mkDosingState Survanta 1 3.

Lemma too_soon_ineligible : ~ repeat_eligible too_soon_state 40.
Proof.
  unfold repeat_eligible, too_soon_state, min_hours_between_doses. simpl. lia.
Qed.

(** Safe repeat dosing requires all eligibility criteria. *)
Definition safe_repeat_dose (ds : DosingState) (fio2 : fio2_pct)
                            (c : Contraindications) (dose : nat) : Prop :=
  repeat_eligible ds fio2 /\
  no_contraindications c /\
  dose_valid dose.

(** Repeat dose is safe only when timing constraint met. *)
Theorem repeat_safe_requires_timing :
  forall ds fio2 c dose,
    hours_since_last ds < min_hours_between_doses (product ds) ->
    ~ safe_repeat_dose ds fio2 c dose.
Proof.
  intros ds fio2 c dose Htoo_soon.
  unfold safe_repeat_dose, repeat_eligible.
  intros [[_ [Hhours _]] _].
  lia.
Qed.

(** Repeat dose is safe only when under max doses. *)
Theorem repeat_safe_requires_under_max :
  forall ds fio2 c dose,
    doses_given ds >= max_doses (product ds) ->
    ~ safe_repeat_dose ds fio2 c dose.
Proof.
  intros ds fio2 c dose Hover.
  unfold safe_repeat_dose, repeat_eligible.
  intros [[Hunder _] _].
  lia.
Qed.

(** All repeat criteria met implies repeat is safe. *)
Theorem repeat_safe_when_eligible :
  forall ds fio2 c dose,
    repeat_eligible ds fio2 ->
    no_contraindications c ->
    dose_valid dose ->
    safe_repeat_dose ds fio2 c dose.
Proof.
  intros ds fio2 c dose Helig Hcontra Hdose.
  unfold safe_repeat_dose. auto.
Qed.

(** -------------------------------------------------------------------------- *)
(** Non-Responder Pathway                                                       *)
(** -------------------------------------------------------------------------- *)

(** Surfactant response assessment: check if FiO2 improved post-dose.
    Non-response suggests alternate diagnosis or need for repeat. *)
Inductive SurfactantResponse : Type :=
  | Responded        (* FiO2 decreased significantly post-dose *)
  | PartialResponse  (* Some improvement but still elevated FiO2 *)
  | NonResponder.    (* No improvement or worsening *)

(** Response assessment based on FiO2 change. *)
Definition assess_response (fio2_pre fio2_post : fio2_pct)
                           (hours_post_dose : nat) : SurfactantResponse :=
  if hours_post_dose <? 2 then
    PartialResponse  (* Too early to assess *)
  else if fio2_post <=? (fio2_pre - 10) then
    Responded
  else if fio2_post <? fio2_pre then
    PartialResponse
  else
    NonResponder.

(** Non-responder requires re-evaluation. *)
Definition requires_reevaluation (resp : SurfactantResponse) : Prop :=
  resp = NonResponder.

(** Non-responder differential: conditions that mimic RDS but don't respond. *)
Inductive NonResponderDifferential : Type :=
  | PersistentPulmonaryHypertension
  | CongenitalPneumonia
  | CongenitalHeartDisease
  | SurfactantProteinDeficiency
  | AlveolarCapillaryDysplasia.

(** --- Witness: 50% to 35% FiO2 at 3h = responded --- *)
Lemma response_good_example : assess_response 50 35 3 = Responded.
Proof. reflexivity. Qed.

(** --- Witness: 50% to 52% FiO2 at 3h = non-responder (worsened) --- *)
Lemma response_poor_example : assess_response 50 52 3 = NonResponder.
Proof. reflexivity. Qed.

(** --- Witness: Any assessment at 1h = partial (too early) --- *)
Lemma response_early_example : assess_response 50 35 1 = PartialResponse.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Weaning Criteria                                                            *)
(** -------------------------------------------------------------------------- *)

(** Weaning readiness thresholds. *)
Definition weaning_fio2_threshold : nat := 25.  (* FiO2 <= 25% *)
Definition weaning_spo2_low : nat := 90.        (* SpO2 >= 90% *)
Definition weaning_spo2_high : nat := 94.       (* SpO2 <= 94% *)

(** Ready to wean from respiratory support. *)
Definition ready_to_wean (fio2 : fio2_pct) (spo2 : spo2_pct)
                         (work_of_breathing_increased : bool) : Prop :=
  fio2 <= weaning_fio2_threshold /\
  spo2 >= weaning_spo2_low /\
  spo2 <= weaning_spo2_high /\
  work_of_breathing_increased = false.

(** --- Witness: FiO2 21%, SpO2 92%, no WOB → ready to wean --- *)
Lemma wean_ready_example : ready_to_wean 21 92 false.
Proof.
  unfold ready_to_wean, weaning_fio2_threshold,
         weaning_spo2_low, weaning_spo2_high.
  repeat split; try lia; try reflexivity.
Qed.

(** --- Counterexample: FiO2 35% → not ready --- *)
Lemma wean_high_fio2_not_ready : ~ ready_to_wean 35 92 false.
Proof.
  unfold ready_to_wean, weaning_fio2_threshold. intros [Hfio2 _]. lia.
Qed.

(** --- Counterexample: Increased WOB → not ready --- *)
Lemma wean_increased_wob_not_ready : ~ ready_to_wean 21 92 true.
Proof.
  unfold ready_to_wean. intros [_ [_ [_ Hwob]]]. discriminate.
Qed.

(** -------------------------------------------------------------------------- *)
(** Integrated Clinical Decision (PRIMARY DECISION PREDICATE)                  *)
(** -------------------------------------------------------------------------- *)

(** THIS IS THE PRIMARY DECISION PREDICATE for clinical use.
    Unlike the core indication predicates (surfactant_indicated), this
    integrates all clinically relevant factors:
    - Patient validity (physiological bounds)
    - Contraindication screening
    - Timing constraints (prophylactic window)
    - CXR consistency (rescue pathway)
    - CPAP trial context (rescue pathway)

    Use surfactant_recommendation for actual clinical decision support.
    Use recommend_surfactant in extraction for runtime decisions. *)

(** Complete clinical state for surfactant decision. *)
Record ClinicalState := mkClinicalState {
  cs_patient : Patient;
  cs_signs : RDSSigns;
  cs_contraindications : Contraindications;
  cs_imaging : ImagingEvidence;
  cs_blood_gas : BloodGas;
  cs_minutes_since_birth : minutes_since_birth;
  cs_cpap_trial : option CPAPTrialState;
  cs_current_support : RespiratorySupport
}.

(** Prophylactic pathway: GA < 30+0w (< 210 days), intubated for stabilization,
    within timing window, no contraindications. Per European Consensus 2022. *)
Definition prophylactic_recommendation (cs : ClinicalState) : Prop :=
  ga_total_days (cs_patient cs) < 210 /\
  cs_current_support cs = Intubated /\
  within_prophylactic_window (cs_minutes_since_birth cs) /\
  no_contraindications (cs_contraindications cs).

(** Rescue pathway: FiO2 elevated, clinical signs, imaging/blood gas evidence.
    NOTE: This is MORE CONSERVATIVE than European 2022 guideline, which states
    FiO2 > 30% on CPAP ≥6 cmH2O is sufficient to trigger surfactant.
    We additionally require: imaging OR blood gas OR clinical_judgement flag.
    This design choice adds a confirmation gate beyond FiO2/CPAP thresholds.
    For strict guideline-minimal logic, set clinical_judgement = true. *)
Definition rescue_recommendation (cs : ClinicalState) : Prop :=
  fio2_elevated (current_fio2 (cs_patient cs)) /\
  clinical_rds (cs_signs cs) /\
  (* Imaging OR blood gas OR clinical judgement required - conservative gate *)
  (imaging_supports_rds (cs_imaging cs) \/
   blood_gas_supports_surfactant (cs_blood_gas cs)) /\
  no_contraindications (cs_contraindications cs) /\
  match cs_current_support cs with
  | Intubated => True  (* Already intubated, no CPAP trial needed *)
  | CPAP => match cs_cpap_trial cs with
            | None => False  (* On CPAP but no trial data - invalid state *)
            | Some trial => cpap_trial_failed trial
            end
  | RoomAir => False  (* Must be on respiratory support for rescue *)
  end.

(** Guideline-minimal rescue: literal European 2022 rule.
    FiO2 > 30% on CPAP ≥6 (or already intubated) is sufficient.
    No imaging/blood gas gate required. *)
Definition rescue_guideline_minimal (cs : ClinicalState) : Prop :=
  fio2_elevated (current_fio2 (cs_patient cs)) /\
  clinical_rds (cs_signs cs) /\
  no_contraindications (cs_contraindications cs) /\
  match cs_current_support cs with
  | Intubated => True
  | CPAP => match cs_cpap_trial cs with
            | None => False
            | Some trial => cpap_trial_failed trial
            end
  | RoomAir => False
  end.

(** Our conservative rule implies the guideline rule.
    If we recommend rescue, the guideline would too. *)
Theorem conservative_implies_guideline :
  forall cs, rescue_recommendation cs -> rescue_guideline_minimal cs.
Proof.
  intros cs [Hfio2 [Hsigns [_ [Hcontra Hsupport]]]].
  unfold rescue_guideline_minimal.
  auto.
Qed.

(** Witness: Case where guideline recommends but we don't.
    FiO2 elevated, CPAP failed, but no imaging/blood gas evidence. *)
Definition guideline_only_case : ClinicalState :=
  mkClinicalState
    (mkPatient 30 0 1200 12 50)         (* 30+0w, 1200g, 12h old, FiO2 50% *)
    (mkRDSSigns true true false false) (* Grunting, retractions *)
    clear_contraindications
    (mkImagingEvidence None None false) (* No imaging, no clinical override *)
    (mkBloodGas 7320 48 65)            (* Normal-ish gas, no acidosis *)
    720                                 (* 12 hours *)
    (Some failed_cpap_trial)
    CPAP.

(** Guideline recommends for this case. *)
Lemma guideline_recommends_case : rescue_guideline_minimal guideline_only_case.
Proof.
  unfold rescue_guideline_minimal, guideline_only_case. simpl.
  split. { unfold fio2_elevated, fio2_threshold. lia. }
  split. { unfold clinical_rds, sign_count. simpl. lia. }
  split. { exact clear_contraindications_ok. }
  exact failed_cpap_trial_indicates_surfactant.
Qed.

(** We do NOT recommend for this case (no imaging/blood gas evidence). *)
Lemma conservative_rejects_case : ~ rescue_recommendation guideline_only_case.
Proof.
  unfold rescue_recommendation, guideline_only_case. simpl.
  intros [_ [_ [Hevidence _]]].
  destruct Hevidence as [Himg | Hgas].
  - unfold imaging_supports_rds in Himg. simpl in Himg.
    destruct Himg as [H | [H | H]]; try contradiction; discriminate.
  - unfold blood_gas_supports_surfactant, respiratory_acidosis,
           ph_critical_low, pco2_critical_high in Hgas. simpl in Hgas.
    destruct Hgas as [H | H].
    + apply Nat.ltb_ge in H. discriminate.
    + apply Nat.ltb_ge in H. discriminate.
Qed.

(** Unified recommendation: prophylactic OR rescue pathway. *)
Definition surfactant_recommendation (cs : ClinicalState) : Prop :=
  valid_patient (cs_patient cs) /\
  (prophylactic_recommendation cs \/ rescue_recommendation cs).

(** --- Witness: Complete prophylactic case --- *)
Definition prophylactic_case : ClinicalState :=
  mkClinicalState
    (mkPatient 28 0 900 0 40)          (* 28+0w, 900g, just born, on O2 *)
    (mkRDSSigns false false false false) (* No signs yet *)
    clear_contraindications
    (mkImagingEvidence None None false) (* No imaging yet - not needed for prophylactic *)
    (mkBloodGas 7350 40 70)           (* Normal gas *)
    5                                  (* 5 minutes old *)
    None                               (* No CPAP trial *)
    Intubated.                         (* Intubated for stabilization *)

Lemma prophylactic_case_recommended : surfactant_recommendation prophylactic_case.
Proof.
  unfold surfactant_recommendation, prophylactic_case. split.
  - unfold valid_patient. simpl.
    repeat split; apply Nat.leb_le; reflexivity.
  - left. unfold prophylactic_recommendation, ga_total_days. simpl.
    repeat split; try exact clear_contraindications_ok.
    + lia.
    + unfold within_prophylactic_window, prophylactic_window_minutes. lia.
Qed.

(** --- Witness: Complete rescue case --- *)
Definition rescue_case : ClinicalState :=
  mkClinicalState
    (mkPatient 28 0 1100 6 50)         (* 28+0w, 1100g, 6h old, FiO2 50% *)
    (mkRDSSigns true true true false) (* Grunting, retractions, flaring *)
    clear_contraindications
    cxr_evidence                       (* CXR shows RDS *)
    (mkBloodGas 7250 55 50)           (* Mild acidosis *)
    360                                (* 6 hours = 360 minutes *)
    (Some failed_cpap_trial)          (* CPAP trial failed *)
    CPAP.

Lemma rescue_case_recommended : surfactant_recommendation rescue_case.
Proof.
  unfold surfactant_recommendation, rescue_case. split.
  - unfold valid_patient. simpl.
    repeat split; apply Nat.leb_le; reflexivity.
  - right. unfold rescue_recommendation. simpl. split.
    + unfold fio2_elevated, fio2_threshold. lia.
    + split.
      * unfold clinical_rds, sign_count. simpl. lia.
      * split.
        { left. exact cxr_evidence_supports. }
        { split.
          - exact clear_contraindications_ok.
          - exact failed_cpap_trial_indicates_surfactant. }
Qed.

(** --- Counterexample: Contraindication blocks despite meeting other criteria --- *)
Definition contraindicated_case : ClinicalState :=
  mkClinicalState
    (mkPatient 28 0 900 0 21)           (* Would qualify by GA, room air *)
    (mkRDSSigns false false false false)
    cdh_present                        (* CDH present - blocks! *)
    (mkImagingEvidence None None false) (* No imaging *)
    (mkBloodGas 7350 40 70)
    5                                  (* Within timing window *)
    None
    Intubated.                         (* Intubated *)

Lemma contraindicated_case_not_recommended : ~ surfactant_recommendation contraindicated_case.
Proof.
  unfold surfactant_recommendation, contraindicated_case.
  intros [_ [Hpro | Hres]].
  - unfold prophylactic_recommendation in Hpro. simpl in Hpro.
    destruct Hpro as [_ [_ [_ Hno]]].
    apply cdh_not_clear. exact Hno.
  - unfold rescue_recommendation in Hres. simpl in Hres.
    destruct Hres as [Hfio2 _].
    unfold fio2_elevated, fio2_threshold in Hfio2.
    apply Nat.lt_nge in Hfio2. apply Hfio2.
    apply Nat.leb_le. reflexivity.
Qed.

(** -------------------------------------------------------------------------- *)
(** Safety Theorems                                                            *)
(** -------------------------------------------------------------------------- *)

(** Safe to give surfactant requires:
    1. Valid patient within physiological bounds
    2. Clinical indication present (prophylactic or rescue)
    3. No contraindications
    4. Valid dose *)
Definition safe_to_give (p : Patient) (signs : RDSSigns)
                        (c : Contraindications) (dose : nat) : Prop :=
  valid_patient p /\
  surfactant_indicated p signs /\
  no_contraindications c /\
  dose_valid dose.

(** Product-aware safe to give: uses product-specific dose limits. *)
Definition safe_to_give_product (p : Patient) (signs : RDSSigns)
                                (c : Contraindications)
                                (prod : SurfactantProduct) (dose : nat) : Prop :=
  valid_patient p /\
  surfactant_indicated p signs /\
  no_contraindications c /\
  dose_valid_for_product prod dose.

(** All preconditions met implies administration is safe. *)
Theorem administration_safe :
  forall p signs c dose,
    valid_patient p ->
    surfactant_indicated p signs ->
    no_contraindications c ->
    dose_valid dose ->
    safe_to_give p signs c dose.
Proof.
  intros p signs c dose Hvalid Hind Hcontra Hdose.
  unfold safe_to_give. auto.
Qed.

(** Product-aware administration is safe when preconditions met. *)
Theorem administration_safe_product :
  forall p signs c prod dose,
    valid_patient p ->
    surfactant_indicated p signs ->
    no_contraindications c ->
    dose_valid_for_product prod dose ->
    safe_to_give_product p signs c prod dose.
Proof.
  intros p signs c prod dose Hvalid Hind Hcontra Hdose.
  unfold safe_to_give_product. auto.
Qed.

(** Any contraindication blocks safe administration.
    Key safety property: even if indicated, contraindications
    must prevent administration. *)
Theorem contraindication_blocks_administration :
  forall p signs c dose,
    has_contraindication c ->
    ~ safe_to_give p signs c dose.
Proof.
  intros p signs c dose Hcontra.
  unfold safe_to_give. intros [_ [_ [Hno _]]].
  unfold has_contraindication in Hcontra.
  unfold no_contraindications in Hno.
  destruct Hno as [Hcdh [Hlethal [Hhypo [Hhem Hpneu]]]].
  destruct Hcontra as [H | [H | [H | [H | H]]]];
    rewrite H in *; discriminate.
Qed.

(** Corollary: CDH specifically blocks administration. *)
Corollary cdh_blocks_administration :
  forall p signs dose,
    ~ safe_to_give p signs cdh_present dose.
Proof.
  intros p signs dose.
  apply contraindication_blocks_administration.
  exact cdh_is_contraindication.
Qed.

(** Well infant (GA >= 30+0, FiO2 <= 30) is never indicated.
    Substantive: proves the decision logic correctly excludes
    term or near-term infants not in respiratory distress. *)
Theorem well_infant_not_indicated :
  forall p signs,
    ga_total_days p >= 210 ->
    current_fio2 p <= fio2_threshold ->
    ~ surfactant_indicated p signs.
Proof.
  intros p signs Hga Hfio2.
  unfold surfactant_indicated. intros [Hpro | Hres].
  - unfold prophylactic_indicated in Hpro. lia.
  - unfold rescue_indicated in Hres. destruct Hres as [Hfio2_elev _].
    unfold fio2_elevated in Hfio2_elev. lia.
Qed.

(** Withholding from well infant does not miss indication. *)
Theorem withhold_well_infant_safe :
  forall p signs c dose,
    ga_total_days p >= 210 ->
    current_fio2 p <= fio2_threshold ->
    ~ safe_to_give p signs c dose.
Proof.
  intros p signs c dose Hga Hfio2.
  unfold safe_to_give. intros [_ [Hind _]].
  apply (well_infant_not_indicated p signs Hga Hfio2). exact Hind.
Qed.

(** Dose from calculation is bounded for valid weights.
    Uses: max weight 3000g * max rate 200mg/kg / 1000 = 600mg. *)
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

  Lemma fio2_elevated_reflect : forall f,
    fio2_elevated_dec f = true <-> fio2_elevated f.
  Proof.
    intros f. unfold fio2_elevated_dec, fio2_elevated.
    apply Nat.ltb_lt.
  Qed.

  (** Decidable prophylactic indication using total days. *)
  Definition prophylactic_indicated_dec (p : Patient) : bool :=
    ga_total_days p <? 210.

  Lemma prophylactic_indicated_reflect : forall p,
    prophylactic_indicated_dec p = true <-> prophylactic_indicated p.
  Proof.
    intros p. unfold prophylactic_indicated_dec, prophylactic_indicated.
    apply Nat.ltb_lt.
  Qed.

  (** Decidable clinical RDS (>= 2 signs). *)
  Definition clinical_rds_dec (s : RDSSigns) : bool :=
    2 <=? sign_count s.

  Lemma clinical_rds_reflect : forall s,
    clinical_rds_dec s = true <-> clinical_rds s.
  Proof.
    intros s. unfold clinical_rds_dec, clinical_rds.
    apply Nat.leb_le.
  Qed.

  (** Calculate initial dose. *)
  Definition calc_initial_dose (prod : SurfactantProduct) (wt : weight_g) : nat :=
    initial_dose prod wt.

  (** Calculate repeat dose. *)
  Definition calc_repeat_dose (prod : SurfactantProduct) (wt : weight_g) : nat :=
    repeat_dose prod wt.

  (** Check CPAP failure. *)
  Definition cpap_failed_dec (pressure : nat) (fio2 : fio2_pct) : bool :=
    (cpap_min_pressure <=? pressure) && (cpap_fio2_failure_threshold <? fio2).

  Lemma cpap_failed_reflect : forall trial,
    cpap_failed_dec (cpap_pressure_cmh2o trial) (fio2_on_cpap trial) = true <->
    cpap_trial_failed trial.
  Proof.
    intros trial. unfold cpap_failed_dec, cpap_trial_failed.
    rewrite Bool.andb_true_iff, Nat.leb_le, Nat.ltb_lt. reflexivity.
  Qed.

  (** Check respiratory acidosis. *)
  Definition acidosis_dec (ph_val : ph_scaled) (pco2_val : pco2_mmhg) : bool :=
    (ph_val <? ph_critical_low) || (pco2_critical_high <? pco2_val).

  Lemma acidosis_reflect : forall bg,
    acidosis_dec (ph bg) (pco2 bg) = true <-> respiratory_acidosis bg.
  Proof.
    intros bg. unfold acidosis_dec, respiratory_acidosis.
    rewrite Bool.orb_true_iff, !Nat.ltb_lt. reflexivity.
  Qed.

  (** Decidable contraindication check. *)
  Definition no_contraindications_dec (c : Contraindications) : bool :=
    negb (congenital_diaphragmatic_hernia c) &&
    negb (lethal_anomaly c) &&
    negb (pulmonary_hypoplasia c) &&
    negb (active_pulmonary_hemorrhage c) &&
    negb (pneumothorax_untreated c).

  Lemma no_contraindications_reflect : forall c,
    no_contraindications_dec c = true <-> no_contraindications c.
  Proof.
    intros c. unfold no_contraindications_dec, no_contraindications.
    repeat rewrite Bool.andb_true_iff.
    repeat rewrite Bool.negb_true_iff.
    destruct c; simpl; tauto.
  Qed.

  (** Decidable CXR consistent with RDS. *)
  Definition cxr_consistent_dec (cxr : ChestXRay) : bool :=
    ground_glass_opacity cxr ||
    (air_bronchograms cxr && low_lung_volumes cxr).

  Lemma cxr_consistent_reflect : forall cxr,
    cxr_consistent_dec cxr = true <-> cxr_consistent_with_rds cxr.
  Proof.
    intros cxr. unfold cxr_consistent_dec, cxr_consistent_with_rds.
    rewrite Bool.orb_true_iff, Bool.andb_true_iff.
    destruct cxr; simpl; tauto.
  Qed.

  (** Decidable ultrasound consistent with RDS. *)
  Definition ultrasound_consistent_dec (us : LungUltrasound) : bool :=
    bilateral_white_lung us ||
    (consolidations us && pleural_irregularity us).

  Lemma ultrasound_consistent_reflect : forall us,
    ultrasound_consistent_dec us = true <-> ultrasound_consistent_with_rds us.
  Proof.
    intros us. unfold ultrasound_consistent_dec, ultrasound_consistent_with_rds.
    rewrite Bool.orb_true_iff, Bool.andb_true_iff.
    destruct us; simpl; tauto.
  Qed.

  (** Decidable imaging supports RDS: CXR OR ultrasound OR clinical judgement. *)
  Definition imaging_supports_dec (ie : ImagingEvidence) : bool :=
    match ie_cxr ie with
    | Some cxr => cxr_consistent_dec cxr
    | None => false
    end ||
    match ie_ultrasound ie with
    | Some us => ultrasound_consistent_dec us
    | None => false
    end ||
    ie_clinical_judgement ie.

  Lemma imaging_supports_reflect : forall ie,
    imaging_supports_dec ie = true <-> imaging_supports_rds ie.
  Proof.
    intros ie. unfold imaging_supports_dec, imaging_supports_rds.
    repeat rewrite Bool.orb_true_iff.
    destruct (ie_cxr ie) as [cxr|] eqn:Hcxr;
    destruct (ie_ultrasound ie) as [us|] eqn:Hus;
    try rewrite cxr_consistent_reflect;
    try rewrite ultrasound_consistent_reflect;
    destruct (ie_clinical_judgement ie); simpl; tauto.
  Qed.

  (** Decidable timing window check. *)
  Definition within_timing_window_dec (mins : minutes_since_birth) : bool :=
    mins <=? prophylactic_window_minutes.

  Lemma within_timing_window_reflect : forall mins,
    within_timing_window_dec mins = true <-> within_prophylactic_window mins.
  Proof.
    intros mins. unfold within_timing_window_dec, within_prophylactic_window.
    apply Nat.leb_le.
  Qed.

  (** Decidable patient validity. *)
  Definition valid_patient_dec (p : Patient) : bool :=
    (22 <=? ga_weeks p) && (ga_weeks p <=? 42) &&
    (ga_days p <=? 6) &&
    (200 <=? birth_weight p) && (birth_weight p <=? 6000) &&
    (21 <=? current_fio2 p) && (current_fio2 p <=? 100).

  Lemma valid_patient_reflect : forall p,
    valid_patient_dec p = true <-> valid_patient p.
  Proof.
    intros p. unfold valid_patient_dec, valid_patient.
    repeat rewrite Bool.andb_true_iff.
    repeat rewrite Nat.leb_le.
    tauto.
  Qed.

  (** Decidable surfactant indication. *)
  Definition surfactant_indicated_dec (p : Patient) (signs : RDSSigns) : bool :=
    prophylactic_indicated_dec p ||
    (fio2_elevated_dec (current_fio2 p) && clinical_rds_dec signs).

  Lemma surfactant_indicated_reflect : forall p signs,
    surfactant_indicated_dec p signs = true <-> surfactant_indicated p signs.
  Proof.
    intros p signs. unfold surfactant_indicated_dec, surfactant_indicated,
      rescue_indicated.
    rewrite Bool.orb_true_iff, Bool.andb_true_iff.
    rewrite prophylactic_indicated_reflect, fio2_elevated_reflect,
      clinical_rds_reflect.
    reflexivity.
  Qed.

  (** Decidable prophylactic recommendation. *)
  Definition prophylactic_rec_dec (p : Patient)
                                  (support : RespiratorySupport)
                                  (mins : minutes_since_birth)
                                  (c : Contraindications) : bool :=
    prophylactic_indicated_dec p &&
    match support with Intubated => true | _ => false end &&
    within_timing_window_dec mins &&
    no_contraindications_dec c.

  Lemma prophylactic_rec_reflect : forall cs,
    prophylactic_rec_dec (cs_patient cs)
                         (cs_current_support cs)
                         (cs_minutes_since_birth cs)
                         (cs_contraindications cs) = true <->
    prophylactic_recommendation cs.
  Proof.
    intros cs. unfold prophylactic_rec_dec, prophylactic_recommendation.
    repeat rewrite Bool.andb_true_iff.
    rewrite prophylactic_indicated_reflect, within_timing_window_reflect,
      no_contraindications_reflect.
    destruct (cs_current_support cs); simpl; intuition discriminate.
  Qed.

  (** Decidable blood gas supports surfactant. *)
  Definition blood_gas_supports_dec (bg : BloodGas) : bool :=
    (ph bg <? ph_critical_low) || (pco2_critical_high <? pco2 bg).

  Lemma blood_gas_supports_reflect : forall bg,
    blood_gas_supports_dec bg = true <-> blood_gas_supports_surfactant bg.
  Proof.
    intros bg. unfold blood_gas_supports_dec, blood_gas_supports_surfactant.
    apply acidosis_reflect.
  Qed.

  (** Decidable rescue recommendation. *)
  Definition rescue_rec_dec (fio2 : fio2_pct) (signs : RDSSigns)
                            (imaging : ImagingEvidence) (bg : BloodGas)
                            (c : Contraindications)
                            (support : RespiratorySupport)
                            (cpap_trial : option CPAPTrialState) : bool :=
    fio2_elevated_dec fio2 &&
    clinical_rds_dec signs &&
    (imaging_supports_dec imaging || blood_gas_supports_dec bg) &&
    no_contraindications_dec c &&
    match support with
    | Intubated => true
    | CPAP => match cpap_trial with
              | None => false
              | Some trial => cpap_failed_dec (cpap_pressure_cmh2o trial)
                                              (fio2_on_cpap trial)
              end
    | RoomAir => false
    end.

  Lemma rescue_rec_reflect : forall cs,
    rescue_rec_dec (current_fio2 (cs_patient cs))
                   (cs_signs cs)
                   (cs_imaging cs)
                   (cs_blood_gas cs)
                   (cs_contraindications cs)
                   (cs_current_support cs)
                   (cs_cpap_trial cs) = true <->
    rescue_recommendation cs.
  Proof.
    intros cs. unfold rescue_rec_dec, rescue_recommendation.
    repeat rewrite Bool.andb_true_iff.
    rewrite Bool.orb_true_iff.
    rewrite fio2_elevated_reflect, clinical_rds_reflect,
      imaging_supports_reflect, blood_gas_supports_reflect,
      no_contraindications_reflect.
    destruct (cs_current_support cs) eqn:Hsup.
    - (* RoomAir *) simpl. intuition.
    - (* CPAP *) destruct (cs_cpap_trial cs) as [trial|] eqn:Htrial.
      + rewrite cpap_failed_reflect. tauto.
      + simpl. intuition.
    - (* Intubated *) simpl. tauto.
  Qed.

  (** Main unified recommendation function.
      Returns true only if patient is valid AND indication criteria are met. *)
  Definition recommend_surfactant (cs : ClinicalState) : bool :=
    valid_patient_dec (cs_patient cs) &&
    (prophylactic_rec_dec (cs_patient cs)
                          (cs_current_support cs)
                          (cs_minutes_since_birth cs)
                          (cs_contraindications cs) ||
     rescue_rec_dec (current_fio2 (cs_patient cs))
                    (cs_signs cs)
                    (cs_imaging cs)
                    (cs_blood_gas cs)
                    (cs_contraindications cs)
                    (cs_current_support cs)
                    (cs_cpap_trial cs)).

  Theorem recommend_surfactant_reflect : forall cs,
    recommend_surfactant cs = true <-> surfactant_recommendation cs.
  Proof.
    intros cs. unfold recommend_surfactant, surfactant_recommendation.
    rewrite Bool.andb_true_iff, Bool.orb_true_iff.
    rewrite valid_patient_reflect, prophylactic_rec_reflect, rescue_rec_reflect.
    reflexivity.
  Qed.

  (** ---------- RUNTIME SAFETY ----------

      The nat -> OCaml int extraction requires care with negative values.
      Use recommend_surfactant_safe as the primary entry point:

        1. Call recommend_surfactant_safe with your ClinicalState
        2. Match on the result:
           - InvalidInput: integer field out of expected range
           - InvalidPatient: patient parameters clinically invalid
           - NotIndicated: valid case, surfactant not recommended
           - Indicated: valid case, surfactant recommended

      OCaml callers should ensure all integer fields are >= 0 before
      constructing records. The validate_clinical_state function catches
      out-of-range values; recommend_surfactant_safe returns InvalidInput
      if validation fails. *)

  (** Validate integer is within bounds. In extracted OCaml, callers must
      first check n >= 0 before passing to these functions. *)
  Definition in_range (n min max : nat) : bool :=
    (min <=? n) && (n <=? max).

  (** Validate Patient fields. *)
  Definition validate_patient (p : Patient) : bool :=
    in_range (ga_weeks p) 22 42 &&
    (ga_days p <=? 6) &&
    in_range (birth_weight p) 200 6000 &&
    in_range (current_fio2 p) 21 100.

  (** Validate BloodGas fields (pH scaled, pCO2, pO2 all reasonable). *)
  Definition validate_blood_gas (bg : BloodGas) : bool :=
    in_range (ph bg) 6800 7800 &&
    in_range (pco2 bg) 10 150 &&
    in_range (po2 bg) 10 500.

  (** Validate CPAPTrialState fields. *)
  Definition validate_cpap_trial (trial : CPAPTrialState) : bool :=
    in_range (cpap_pressure_cmh2o trial) 0 20 &&
    in_range (fio2_on_cpap trial) 21 100.

  (** Validate complete ClinicalState. *)
  Definition validate_clinical_state (cs : ClinicalState) : bool :=
    validate_patient (cs_patient cs) &&
    validate_blood_gas (cs_blood_gas cs) &&
    in_range (cs_minutes_since_birth cs) 0 10080 &&  (* up to 7 days *)
    match cs_cpap_trial cs with
    | None => true
    | Some trial => validate_cpap_trial trial
    end.

  (** Recommendation result type for explicit validation feedback. *)
  Inductive RecommendationResult : Type :=
    | InvalidInput        (* Input values out of range *)
    | InvalidPatient      (* Patient failed clinical validity checks *)
    | NotIndicated        (* Valid patient but no indication *)
    | Indicated.          (* Valid patient with indication *)

  (** Safe recommendation: validates all inputs before processing.
      This is the PRIMARY ENTRY POINT for OCaml callers. *)
  Definition recommend_surfactant_safe (cs : ClinicalState) : RecommendationResult :=
    if negb (validate_clinical_state cs) then
      InvalidInput
    else if negb (valid_patient_dec (cs_patient cs)) then
      InvalidPatient
    else if recommend_surfactant cs then
      Indicated
    else
      NotIndicated.

End SurfactantDecision.

(** Extract the decision module. *)
Extraction "surfactant_decision.ml" SurfactantDecision.
