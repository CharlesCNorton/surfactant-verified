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

   [4] Verder H, Agertoft L, Albertsen P, et al.
       "RDS-NExT Workshop: Consensus Statements for the Use of Surfactant
       in Preterm Neonates with RDS."
       J Perinatol. 2023;43:1112-1120.
       doi:10.1038/s41372-023-01690-9

   [5] Defined by Network Meta-analysis.
       "Clinical Decision Thresholds for Surfactant Administration in
       Preterm Infants: A Systematic Review and Network Meta-analysis."
       eClinicalMedicine. 2023;62:102097.
       doi:10.1016/j.eclinm.2023.102097

   [6] Walsh BK, Daigle B, DiBlasi RM, Restrepo RD.
       "AARC Clinical Practice Guideline: Surfactant Replacement Therapy."
       Respir Care. 2013;58(2):367-375.
       doi:10.4187/respcare.02189

   [7] Canadian Paediatric Society, Fetus and Newborn Committee.
       "Guidelines for Surfactant Replacement Therapy in Neonates."
       Paediatr Child Health. 2021;26(1):35-41.
       doi:10.1093/pch/pxaa116

   [8] Protocure Project (Formal Methods for Medical Protocols):
       - Marcos M, et al. "Verification of Medical Guidelines in KIV."
         AI Commun. 2006;19(3):219-232.
       - Ten Teije A, et al. "From Informal Knowledge to Formal Logic."
         EKAW 2002, LNAI 2473, pp. 95-110.
*)

(** -------------------------------------------------------------------------- *)
(** GAPS AND FURTHER WORK                                                      *)
(** -------------------------------------------------------------------------- *)

(**
   STATUS: STABLE (compiles, no admits, key theorems proven)
   TARGET: EXERCISED (requires external validation)

   TODO:
   1.  Export to UPPAAL timed automata for temporal verification
   2.  Obtain anonymized NICU case records (n >= 50) for validation
   3.  Run recommend_surfactant_safe against historical decisions
   4.  Measure concordance rate with attending neonatologist decisions
   5.  Document false positives/negatives vs. clinician decisions
   6.  Cross-validate: same test cases, same verdicts across tools
*)

From Coq Require Import Arith Lia List.
Import ListNotations.

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

(** Prophylactic surfactant threshold: < 30 weeks (< 210 days) per European
    Consensus 2022. Days-based precision: 29+6 (209 days) qualifies,
    30+0 (210 days) does not. *)
Definition prophylactic_ga_threshold_weeks : nat := 30.
Definition prophylactic_ga_threshold_days : nat := prophylactic_ga_threshold_weeks * 7.

(** Eligible for prophylactic surfactant based on GA. *)
Definition prophylactic_eligible (p : Patient) : Prop :=
  ga_total_days p < prophylactic_ga_threshold_days.

(** Validity predicate: GA, weight, postnatal age, and FiO2 within physiological bounds.
    Postnatal age upper bound of 168 hours (7 days) reflects that surfactant
    therapy is primarily given in the first week of life. *)
Definition valid_patient (p : Patient) : Prop :=
  22 <= ga_weeks p /\ ga_weeks p <= 42 /\
  ga_days p <= 6 /\
  200 <= birth_weight p /\ birth_weight p <= 6000 /\
  age_hours p <= 168 /\
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

(** --- Edge case: Minimum viable GA (22+0 weeks) --- *)
Definition edge_min_ga_patient : Patient :=
  mkPatient 22 0 400 1 30.

Lemma edge_min_ga_valid : valid_patient edge_min_ga_patient.
Proof.
  unfold valid_patient, edge_min_ga_patient. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Edge case: Maximum GA (42+0 weeks) --- *)
Definition edge_max_ga_patient : Patient :=
  mkPatient 42 0 4000 1 21.

Lemma edge_max_ga_valid : valid_patient edge_max_ga_patient.
Proof.
  unfold valid_patient, edge_max_ga_patient. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Edge case: Minimum weight (200g) --- *)
Definition edge_min_weight_patient : Patient :=
  mkPatient 24 0 200 1 40.

Lemma edge_min_weight_valid : valid_patient edge_min_weight_patient.
Proof.
  unfold valid_patient, edge_min_weight_patient. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
Qed.

(** --- Edge case: Maximum weight (6000g) --- *)
Definition edge_max_weight_patient : Patient :=
  mkPatient 40 0 6000 1 21.

Lemma edge_max_weight_valid : valid_patient edge_max_weight_patient.
Proof.
  unfold valid_patient, edge_max_weight_patient. simpl.
  repeat split; apply Nat.leb_le; reflexivity.
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
(** FiO2 Threshold (Parameterized)                                             *)
(** -------------------------------------------------------------------------- *)

(** FiO2 threshold options per various guidelines:
    - 30%: European Consensus 2022 (default, most conservative)
    - 40%: Network meta-analysis [5] suggests for GA >26w
    - 50%: Canadian guidelines [7] *)
Definition fio2_threshold_30 : nat := 30.
Definition fio2_threshold_40 : nat := 40.
Definition fio2_threshold_50 : nat := 50.

(** Default threshold: 30% per European Consensus 2022.
    This constant is the single source of truth used by default predicates. *)
Definition fio2_threshold : nat := fio2_threshold_30.

(** Parameterized FiO2 elevation check. *)
Definition fio2_elevated_at (threshold : nat) (f : fio2_pct) : Prop :=
  f > threshold.

(** FiO2 exceeds default threshold (30%). *)
Definition fio2_elevated (f : fio2_pct) : Prop :=
  fio2_elevated_at fio2_threshold f.

(** Default is instance of parameterized version. *)
Lemma fio2_elevated_is_at_default : forall f,
  fio2_elevated f <-> fio2_elevated_at fio2_threshold_30 f.
Proof.
  intros f. unfold fio2_elevated, fio2_elevated_at, fio2_threshold. reflexivity.
Qed.

(** Higher threshold is more permissive (fewer infants qualify). *)
Lemma higher_threshold_fewer_indications : forall f t1 t2,
  t1 < t2 -> fio2_elevated_at t2 f -> fio2_elevated_at t1 f.
Proof.
  intros f t1 t2 Ht Hf. unfold fio2_elevated_at in *. lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** GA-Stratified Thresholds                                                   *)
(** -------------------------------------------------------------------------- *)

(** Threshold configuration based on gestational age strata.
    Per network meta-analysis [5]:
    - Extremely preterm (<26w): 30% (most conservative)
    - Very preterm (26-28w): 40%
    - Moderate preterm (29-32w): 40%
    - Late preterm (>32w): 50% *)
Definition fio2_threshold_for_ga (ga_weeks : nat) : nat :=
  if ga_weeks <? 26 then fio2_threshold_30
  else if ga_weeks <=? 32 then fio2_threshold_40
  else fio2_threshold_50.

(** GA-aware FiO2 elevation check. *)
Definition fio2_elevated_for_ga (ga_weeks : nat) (f : fio2_pct) : Prop :=
  fio2_elevated_at (fio2_threshold_for_ga ga_weeks) f.

(** Extremely preterm uses strictest threshold (30%). *)
Lemma extreme_preterm_threshold : forall ga,
  ga < 26 -> fio2_threshold_for_ga ga = fio2_threshold_30.
Proof.
  intros ga Hga. unfold fio2_threshold_for_ga.
  apply Nat.ltb_lt in Hga. rewrite Hga. reflexivity.
Qed.

(** Late preterm uses most permissive threshold (50%). *)
Lemma late_preterm_threshold : forall ga,
  ga > 32 -> fio2_threshold_for_ga ga = fio2_threshold_50.
Proof.
  intros ga Hga. unfold fio2_threshold_for_ga.
  assert (H1: (ga <? 26) = false) by (apply Nat.ltb_ge; lia).
  assert (H2: (ga <=? 32) = false) by (apply Nat.leb_gt; lia).
  rewrite H1, H2. reflexivity.
Qed.

(** More mature infants have higher (more permissive) thresholds. *)
Lemma ga_threshold_monotonic : forall ga1 ga2,
  ga1 <= ga2 -> fio2_threshold_for_ga ga1 <= fio2_threshold_for_ga ga2.
Proof.
  intros ga1 ga2 Hga.
  unfold fio2_threshold_for_ga, fio2_threshold_30, fio2_threshold_40, fio2_threshold_50.
  destruct (ga1 <? 26) eqn:E1; destruct (ga2 <? 26) eqn:E2;
  destruct (ga1 <=? 32) eqn:E3; destruct (ga2 <=? 32) eqn:E4;
  try lia; apply Nat.ltb_lt in E1 || apply Nat.ltb_ge in E1;
  apply Nat.ltb_lt in E2 || apply Nat.ltb_ge in E2;
  apply Nat.leb_le in E3 || apply Nat.leb_gt in E3;
  apply Nat.leb_le in E4 || apply Nat.leb_gt in E4; lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** CPAP-First Protocol                                                        *)
(** -------------------------------------------------------------------------- *)

(** Respiratory support modality. Modern guidelines prefer CPAP trial first. *)
Inductive RespiratorySupport : Type :=
  | RoomAir          (* No support *)
  | CPAP             (* Continuous positive airway pressure *)
  | Intubated.       (* Endotracheal tube in place *)

(** CPAP trial state for rescue surfactant decision.
    Duration is recorded for audit/trending but does not gate the failure
    decision: European Consensus 2022 specifies FiO2/pressure thresholds
    without a minimum trial duration. Local protocols may impose additional
    duration requirements before declaring failure. *)
Record CPAPTrialState := mkCPAPTrialState {
  cpap_pressure_cmh2o : nat;    (* Typical 5-8 cmH2O *)
  cpap_duration_minutes : nat;  (* Recorded for audit; not used in failure gate *)
  fio2_on_cpap : fio2_pct       (* FiO2 requirement while on CPAP *)
}.

(** CPAP failure pressure threshold per European Consensus 2022:
    CPAP >= 6 cmH2O with FiO2 > 30% indicates surfactant needed.
    No minimum duration is specified by the guideline. *)
Definition cpap_min_pressure : nat := 6.

(** CPAP trial has failed, surfactant needed. Failure is determined by
    pressure (>= 6 cmH2O) and FiO2 (> 30%) thresholds; duration is not gating. *)
Definition cpap_trial_failed (trial : CPAPTrialState) : Prop :=
  cpap_pressure_cmh2o trial >= cpap_min_pressure /\
  fio2_on_cpap trial > fio2_threshold.

(** Optional CPAP duration gate for local protocols.
    Some sites require minimum trial duration before declaring failure.
    Default: 30 minutes (configurable per institutional policy). *)
Definition cpap_min_duration_minutes : nat := 30.

(** Check if CPAP trial duration is sufficient per local policy. *)
Definition cpap_duration_sufficient (trial : CPAPTrialState) : Prop :=
  cpap_duration_minutes trial >= cpap_min_duration_minutes.

(** CPAP trial failed with duration gate (optional stricter criterion).
    Requires: pressure, FiO2, AND minimum duration before declaring failure. *)
Definition cpap_trial_failed_with_duration (trial : CPAPTrialState) : Prop :=
  cpap_trial_failed trial /\ cpap_duration_sufficient trial.

(** Duration-gated failure is stricter than standard failure. *)
Lemma duration_gate_stricter :
  forall trial, cpap_trial_failed_with_duration trial -> cpap_trial_failed trial.
Proof.
  intros trial [Hfailed _]. exact Hfailed.
Qed.

(** --- Witness: CPAP failure at FiO2 50% on 7 cmH2O --- *)
Definition failed_cpap_trial : CPAPTrialState :=
  mkCPAPTrialState 7 30 50.

Lemma failed_cpap_trial_indicates_surfactant : cpap_trial_failed failed_cpap_trial.
Proof.
  unfold cpap_trial_failed, failed_cpap_trial, cpap_min_pressure,
         fio2_threshold, fio2_threshold_30. simpl. lia.
Qed.

(** --- Counterexample: Stable on CPAP at FiO2 30% --- *)
Definition stable_cpap_trial : CPAPTrialState :=
  mkCPAPTrialState 6 60 30.

Lemma stable_cpap_not_failed : ~ cpap_trial_failed stable_cpap_trial.
Proof.
  unfold cpap_trial_failed, stable_cpap_trial, fio2_threshold, fio2_threshold_30,
         cpap_min_pressure. simpl. lia.
Qed.

(** --- Witness: FiO2 45% exceeds 30% threshold --- *)
Lemma fio2_45_elevated : fio2_elevated 45.
Proof.
  unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. lia.
Qed.

(** --- Counterexample: FiO2 25% does not exceed threshold --- *)
Lemma fio2_25_not_elevated : ~ fio2_elevated 25.
Proof.
  unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. lia.
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
  unfold oxygenation_failure, fio2_elevated, fio2_elevated_at,
         fio2_threshold, fio2_threshold_30, spo2_below_target, spo2_target_low. lia.
Qed.

(** --- Counterexample: FiO2 25% with SpO2 92% = no failure --- *)
Lemma no_oxygenation_failure_example : ~ oxygenation_failure 25 92.
Proof.
  unfold oxygenation_failure, fio2_elevated, fio2_elevated_at,
         fio2_threshold, fio2_threshold_30. lia.
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

(** SF ratio as supporting evidence for surfactant need.
    Used as adjunct criterion in SF-integrated rescue indication. *)
Definition sf_supports_surfactant (spo2 : spo2_pct) (fio2 : fio2_pct) : Prop :=
  sf_impaired spo2 fio2.

(** SF-integrated FiO2 elevation: either FiO2 alone elevated,
    OR moderate FiO2 with impaired SF ratio. *)
Definition fio2_elevated_with_sf (fio2 : fio2_pct) (spo2 : spo2_pct) : Prop :=
  fio2_elevated fio2 \/ (fio2 > 25 /\ sf_impaired spo2 fio2).

(** SF ratio can lower the FiO2 threshold needed for indication. *)
Lemma sf_ratio_lowers_threshold : forall fio2 spo2,
  fio2 > 25 -> sf_impaired spo2 fio2 -> fio2_elevated_with_sf fio2 spo2.
Proof.
  intros fio2 spo2 Hfio2 Hsf. unfold fio2_elevated_with_sf. right. split; auto.
Qed.

(** Standard FiO2 elevation implies SF-integrated elevation. *)
Lemma fio2_elevated_implies_sf_integrated : forall fio2 spo2,
  fio2_elevated fio2 -> fio2_elevated_with_sf fio2 spo2.
Proof.
  intros fio2 spo2 Hfio2. unfold fio2_elevated_with_sf. left. exact Hfio2.
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

(** OI-based escalation pathway recommendations. *)
Inductive OIEscalation : Type :=
  | OI_Standard        (* OI <= 15: standard surfactant therapy *)
  | OI_Severe          (* OI 16-25: consider repeat dose, optimize ventilation *)
  | OI_Critical        (* OI > 25: consult ECMO center, transfer if needed *)
  | OI_ECMO.           (* OI > 40: ECMO initiation likely *)

Definition oi_ecmo_threshold : nat := 40.

(** Classify OI into escalation tier. *)
Definition oi_escalation_tier (oi : nat) : OIEscalation :=
  if oi <=? oi_severe then OI_Standard
  else if oi <=? oi_critical then OI_Severe
  else if oi <=? oi_ecmo_threshold then OI_Critical
  else OI_ECMO.

(** Compute escalation from clinical parameters. *)
Definition escalation_for (fio2 : fio2_pct) (map : map_cmh2o) (pao2 : nat) : OIEscalation :=
  oi_escalation_tier (oxygenation_index fio2 map pao2).

(** --- Witness: OI 4 → Standard tier --- *)
Lemma oi_4_standard : oi_escalation_tier 4 = OI_Standard.
Proof. reflexivity. Qed.

(** --- Witness: OI 20 → Severe tier --- *)
Lemma oi_20_severe : oi_escalation_tier 20 = OI_Severe.
Proof. reflexivity. Qed.

(** --- Witness: OI 30 → Critical tier --- *)
Lemma oi_30_critical : oi_escalation_tier 30 = OI_Critical.
Proof. reflexivity. Qed.

(** --- Witness: OI 50 → ECMO tier --- *)
Lemma oi_50_ecmo : oi_escalation_tier 50 = OI_ECMO.
Proof. reflexivity. Qed.

(** OI determines minimum escalation tier. *)
Lemma oi_above_severe_not_standard : forall oi,
  oi > oi_severe -> oi_escalation_tier oi <> OI_Standard.
Proof.
  intros oi Hoi Hcontra.
  unfold oi_escalation_tier, oi_severe, oi_critical, oi_ecmo_threshold in Hcontra.
  assert (H: (oi <=? 15) = false) by (apply Nat.leb_gt; exact Hoi).
  rewrite H in Hcontra.
  destruct (oi <=? 25); destruct (oi <=? 40); discriminate.
Qed.

(** -------------------------------------------------------------------------- *)
(** Adjunct Metrics Design Note                                                *)
(** -------------------------------------------------------------------------- *)

(** DESIGN DECISION: SF ratio and OI are INFORMATIONAL ONLY.

    These metrics are intentionally excluded from surfactant_recommendation:

    1. SF ratio (SpO2/FiO2): Research correlate of P/F ratio. Useful for
       trending but not validated for surfactant gating in neonates.

    2. Oxygenation Index: Severity metric for ECMO consideration. Indicates
       disease severity but does not gate surfactant (which should be given
       earlier, before OI becomes critical).

    European Consensus 2022 uses FiO2 > 30% on CPAP >= 6 cmH2O as the trigger,
    not SF ratio or OI. These adjunct metrics remain available for:
    - Severity documentation
    - Trend monitoring
    - Research data collection
    - ECMO referral decisions (OI > 25-40)

    To add these to decision logic, modify rescue_recommendation to include
    sf_impaired or oi_indicates_severe. This is NOT RECOMMENDED without
    neonatal-specific validation studies. *)

(** -------------------------------------------------------------------------- *)
(** Lamellar Body Count Biomarker                                              *)
(** -------------------------------------------------------------------------- *)

(** Lamellar body count (LBC) as a biomarker for fetal lung maturity.
    LBC measures surfactant-containing lamellar bodies in amniotic fluid
    or tracheal aspirate. Per literature [5]:
    - LBC < 15,000/μL: immature, high risk of RDS
    - LBC 15,000-50,000/μL: transitional
    - LBC > 50,000/μL: mature, low risk of RDS

    NOTE: LBC is a RESEARCH biomarker, not part of European 2022 guidelines.
    May be useful for risk stratification before delivery. *)

Definition lbc_count := nat.  (* per μL *)

Definition lbc_immature_threshold : nat := 15000.
Definition lbc_mature_threshold : nat := 50000.

Inductive LBCMaturity : Type :=
  | LBC_Immature     (* < 15000: high RDS risk *)
  | LBC_Transitional (* 15000-50000: moderate risk *)
  | LBC_Mature.      (* > 50000: low RDS risk *)

Definition lbc_maturity (lbc : lbc_count) : LBCMaturity :=
  if lbc <? lbc_immature_threshold then LBC_Immature
  else if lbc <=? lbc_mature_threshold then LBC_Transitional
  else LBC_Mature.

(** Immature LBC suggests surfactant deficiency risk. *)
Definition lbc_suggests_deficiency (lbc : lbc_count) : Prop :=
  lbc < lbc_immature_threshold.

(** --- Witness: LBC 10000 is immature --- *)
Lemma lbc_10000_immature : lbc_maturity 10000 = LBC_Immature.
Proof. reflexivity. Qed.

(** --- Witness: LBC 30000 is transitional --- *)
Lemma lbc_30000_transitional : lbc_maturity 30000 = LBC_Transitional.
Proof. reflexivity. Qed.

(** --- Witness: LBC 60000 is mature --- *)
Lemma lbc_60000_mature : lbc_maturity 60000 = LBC_Mature.
Proof. reflexivity. Qed.

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
    Uses days-based GA threshold for precision. *)
Definition prophylactic_complete (p : Patient) (mins : minutes_since_birth)
                                 (support : RespiratorySupport) : Prop :=
  prophylactic_eligible p /\
  within_prophylactic_window mins /\
  support = Intubated.

(** --- Witness: 28+0 week infant at 5 minutes, intubated → criteria met --- *)
Lemma prophylactic_complete_example :
  prophylactic_complete (mkPatient 28 0 900 0 40) 5 Intubated.
Proof.
  unfold prophylactic_complete, prophylactic_eligible, ga_total_days,
         prophylactic_ga_threshold_days, prophylactic_ga_threshold_weeks,
         within_prophylactic_window, prophylactic_window_minutes. simpl.
  repeat split; lia.
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
(** GA Eligibility Witnesses                                                   *)
(** -------------------------------------------------------------------------- *)

(** --- Witness: 25+0 weeks eligible for prophylactic --- *)
Lemma ga_25_0_prophylactic_eligible : prophylactic_eligible (mkPatient 25 0 800 0 21).
Proof.
  unfold prophylactic_eligible, ga_total_days, prophylactic_ga_threshold_days,
         prophylactic_ga_threshold_weeks. simpl. lia.
Qed.

(** --- Witness: 29+6 weeks (209 days) eligible for prophylactic --- *)
Lemma ga_29_6_prophylactic_eligible : prophylactic_eligible (mkPatient 29 6 1200 0 21).
Proof.
  unfold prophylactic_eligible, ga_total_days, prophylactic_ga_threshold_days,
         prophylactic_ga_threshold_weeks. simpl. lia.
Qed.

(** --- Counterexample: 32+0 weeks not eligible for prophylactic --- *)
Lemma ga_32_0_not_prophylactic_eligible : ~ prophylactic_eligible (mkPatient 32 0 1800 0 21).
Proof.
  unfold prophylactic_eligible, ga_total_days, prophylactic_ga_threshold_days,
         prophylactic_ga_threshold_weeks. simpl. lia.
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

(** --- Boundary: Exactly 30+0 weeks (210 days) is NOT prophylactic eligible --- *)
Lemma ga_30_0_not_prophylactic : ~ prophylactic_eligible (mkPatient 30 0 1500 0 21).
Proof.
  unfold prophylactic_eligible, ga_total_days, prophylactic_ga_threshold_days,
         prophylactic_ga_threshold_weeks. simpl. lia.
Qed.

(** --- Boundary: Exactly 30% FiO2 is NOT elevated --- *)
Lemma fio2_30_not_elevated : ~ fio2_elevated 30.
Proof.
  unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. lia.
Qed.

(** --- Boundary: 29+6 (209 days) eligible, 30+0 (210 days) not --- *)
Lemma ga_boundary_29_6_vs_30_0 :
  prophylactic_eligible (mkPatient 29 6 1200 0 21) /\
  ~ prophylactic_eligible (mkPatient 30 0 1500 0 21).
Proof.
  unfold prophylactic_eligible, ga_total_days, prophylactic_ga_threshold_days,
         prophylactic_ga_threshold_weeks. simpl.
  split; lia.
Qed.

(** --- Boundary: 31% is the first elevated FiO2 --- *)
Lemma fio2_boundary_30_vs_31 :
  ~ fio2_elevated 30 /\ fio2_elevated 31.
Proof.
  unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. lia.
Qed.

(** -------------------------------------------------------------------------- *)
(** Indication Logic (Core Criteria)                                           *)
(** -------------------------------------------------------------------------- *)

(** NOTE: These predicates capture the CORE indication criteria only.
    For complete clinical decision-making, use surfactant_recommendation
    which integrates timing, contraindications, CXR, and CPAP context. *)

(** Prophylactic indication (core): GA < 30+0 weeks.
    Uses precise GA including days: 29+6 qualifies, 30+0 doesn't. *)
Definition prophylactic_indicated (p : Patient) : Prop :=
  ga_total_days p < prophylactic_ga_threshold_days.

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
  unfold rescue_indicated, fio2_elevated, fio2_elevated_at,
         fio2_threshold, fio2_threshold_30, rescue_patient,
         clinical_rds, sign_count, rescue_signs. simpl. lia.
Qed.

(** --- Counterexample: 34w infant with FiO2 21% and no signs → not indicated --- *)
Definition well_patient : Patient := mkPatient 34 0 2200 12 21.
Definition well_signs : RDSSigns := mkRDSSigns false false false false.

Lemma well_patient_not_indicated : ~ surfactant_indicated well_patient well_signs.
Proof.
  unfold surfactant_indicated, prophylactic_indicated, ga_total_days,
         prophylactic_ga_threshold_days, prophylactic_ga_threshold_weeks,
         rescue_indicated, fio2_elevated, fio2_elevated_at,
         fio2_threshold, fio2_threshold_30, well_patient. simpl. lia.
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

(** Calculate dose in mg with rounding: (weight_g * dose_per_kg + 500) / 1000.
    Rounds to nearest mg: 849g at 100mg/kg → 85mg (not 84mg with truncation). *)
Definition calculate_dose (weight_g : nat) (dose_per_kg : nat) : nat :=
  (weight_g * dose_per_kg + 500) / 1000.

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

(** Product concentration in mg/mL for volume calculation.
    - Curosurf: 80 mg/mL (1.5 mL and 3 mL vials)
    - Survanta: 25 mg/mL (4 mL and 8 mL vials)
    - Infasurf: 35 mg/mL (3 mL and 6 mL vials) *)
Definition concentration_mg_per_ml (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 25
  | Curosurf => 80
  | Infasurf => 35
  end.

(** Maximum single vial size in mg.
    - Survanta: 8 mL × 25 mg/mL = 200 mg
    - Curosurf: 3 mL × 80 mg/mL = 240 mg
    - Infasurf: 6 mL × 35 mg/mL = 210 mg *)
Definition max_vial_mg (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 200
  | Curosurf => 240
  | Infasurf => 210
  end.

(** Calculate volume in mL (scaled by 10 for precision).
    Returns dose_mg * 10 / concentration, so 160mg Curosurf → 20 (= 2.0 mL). *)
Definition dose_volume_ml_x10 (prod : SurfactantProduct) (dose_mg : nat) : nat :=
  dose_mg * 10 / concentration_mg_per_ml prod.

(** --- Witness: 160mg Curosurf → 2.0 mL (returns 20) --- *)
Lemma curosurf_160mg_volume : dose_volume_ml_x10 Curosurf 160 = 20.
Proof. reflexivity. Qed.

(** --- Witness: 100mg Survanta → 4.0 mL (returns 40) --- *)
Lemma survanta_100mg_volume : dose_volume_ml_x10 Survanta 100 = 40.
Proof. reflexivity. Qed.

(** --- Witness: 105mg Infasurf → 3.0 mL (returns 30) --- *)
Lemma infasurf_105mg_volume : dose_volume_ml_x10 Infasurf 105 = 30.
Proof. reflexivity. Qed.

(** Number of vials needed for a dose (ceiling division). *)
Definition vials_needed (prod : SurfactantProduct) (dose_mg : nat) : nat :=
  (dose_mg + max_vial_mg prod - 1) / max_vial_mg prod.

(** Single vial sufficient for typical preterm weights (concrete witnesses).
    With rounding formula: (weight * dose_per_kg + 500) / 1000 *)

(** --- Witness: 1000g infant, Survanta → 100mg, 1 vial --- *)
Lemma single_vial_survanta_1000g : vials_needed Survanta (initial_dose Survanta 1000) = 1.
Proof. reflexivity. Qed.

(** --- Witness: 1000g infant, Curosurf → 200mg, 1 vial --- *)
Lemma single_vial_curosurf_1000g : vials_needed Curosurf (initial_dose Curosurf 1000) = 1.
Proof. reflexivity. Qed.

(** --- Witness: 1000g infant, Infasurf → 105mg, 1 vial --- *)
Lemma single_vial_infasurf_1000g : vials_needed Infasurf (initial_dose Infasurf 1000) = 1.
Proof. reflexivity. Qed.

(** --- Witness: 800g (typical ELBW), all products single vial --- *)
Lemma single_vial_800g_all :
  vials_needed Survanta (initial_dose Survanta 800) = 1 /\
  vials_needed Curosurf (initial_dose Curosurf 800) = 1 /\
  vials_needed Infasurf (initial_dose Infasurf 800) = 1.
Proof. repeat split; reflexivity. Qed.

(** Dose validity per FDA label: dose matches weight-based mg/kg specification.
    Primary validity check: dose equals expected value from weight calculation. *)
Definition dose_matches_calculation (prod : SurfactantProduct) (weight : weight_g)
                                    (dose : nat) (is_initial : bool) : Prop :=
  dose = if is_initial then initial_dose prod weight
         else repeat_dose prod weight.

(** Dose is positive and correctly calculated. *)
Definition dose_valid_per_kg (prod : SurfactantProduct) (weight : weight_g)
                             (dose : nat) (is_initial : bool) : Prop :=
  dose > 0 /\ dose_matches_calculation prod weight dose is_initial.

(** Local policy maximum single doses (OPTIONAL constraint layer).
    These are site-specific safety caps, not FDA requirements.
    Derivations assume max infant weights of 3-4 kg:
    - Survanta: 100 mg/kg × 4 kg = 400 mg
    - Curosurf: 200 mg/kg × 3 kg = 600 mg
    - Infasurf: 105 mg/kg × 4 kg = 420 mg
    Sites treating larger infants should adjust or remove these caps. *)
Definition local_policy_max_dose (prod : SurfactantProduct) : nat :=
  match prod with
  | Survanta => 400
  | Curosurf => 600
  | Infasurf => 420
  end.

(** Dose within local policy cap (optional additional constraint). *)
Definition dose_within_local_cap (prod : SurfactantProduct) (dose : nat) : Prop :=
  dose <= local_policy_max_dose prod.

(** Dose within acceptable bounds: positive and under local cap.
    Use when weight/calculation info is not available. *)
Definition dose_within_bounds (prod : SurfactantProduct) (dose : nat) : Prop :=
  dose > 0 /\ dose_within_local_cap prod dose.

(** Full validity: per-kg correct AND within local cap.
    Use when weight and initial/repeat info are available. *)
Definition dose_valid_calculated (prod : SurfactantProduct) (weight : weight_g)
                                 (dose : nat) (is_initial : bool) : Prop :=
  dose_valid_per_kg prod weight dose is_initial /\
  dose_within_local_cap prod dose.

(** Alias for compatibility: bounds check only. *)
Definition dose_valid_for_product (prod : SurfactantProduct) (dose : nat) : Prop :=
  dose_within_bounds prod dose.

(** Legacy dose validity (conservative bound for any product). *)
Definition dose_valid (dose : nat) : Prop :=
  dose > 0 /\ dose <= 600.

(** --- Witness: 160mg within Curosurf bounds --- *)
Lemma dose_160_valid_curosurf : dose_valid_for_product Curosurf 160.
Proof.
  unfold dose_valid_for_product, dose_within_bounds,
         dose_within_local_cap, local_policy_max_dose. lia.
Qed.

(** --- Witness: 160mg correctly calculated for 800g Curosurf initial --- *)
Lemma dose_160_calculated_curosurf : dose_valid_calculated Curosurf 800 160 true.
Proof.
  unfold dose_valid_calculated, dose_valid_per_kg, dose_matches_calculation,
         dose_within_local_cap, local_policy_max_dose, initial_dose,
         calculate_dose, initial_dose_per_kg. simpl. lia.
Qed.

(** --- Witness: 100mg within Survanta bounds --- *)
Lemma dose_100_valid_survanta : dose_valid_for_product Survanta 100.
Proof.
  unfold dose_valid_for_product, dose_within_bounds,
         dose_within_local_cap, local_policy_max_dose. lia.
Qed.

(** --- Counterexample: 500mg exceeds Survanta local cap --- *)
Lemma dose_500_exceeds_survanta_cap : ~ dose_valid_for_product Survanta 500.
Proof.
  unfold dose_valid_for_product, dose_within_bounds,
         dose_within_local_cap, local_policy_max_dose. lia.
Qed.

(** --- Counterexample: 700mg exceeds Curosurf local cap --- *)
Lemma dose_700_exceeds_curosurf_cap : ~ dose_valid_for_product Curosurf 700.
Proof.
  unfold dose_valid_for_product, dose_within_bounds,
         dose_within_local_cap, local_policy_max_dose. lia.
Qed.

(** Per-product dose bounds for clinically appropriate weight ranges.
    With rounding: (weight * dose_per_kg + 500) / 1000. *)
Theorem initial_dose_bounded_survanta :
  forall weight, weight <= 4000 ->
    initial_dose Survanta weight <= 400.
Proof.
  intros weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  apply Nat.le_trans with ((4000 * 100 + 500) / 1000).
  - apply Nat.Div0.div_le_mono. lia.
  - apply Nat.leb_le. reflexivity.
Qed.

Theorem initial_dose_bounded_curosurf :
  forall weight, weight <= 3000 ->
    initial_dose Curosurf weight <= 600.
Proof.
  intros weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  apply Nat.le_trans with ((3000 * 200 + 500) / 1000).
  - apply Nat.Div0.div_le_mono. lia.
  - apply Nat.leb_le. reflexivity.
Qed.

Theorem initial_dose_bounded_infasurf :
  forall weight, weight <= 4000 ->
    initial_dose Infasurf weight <= 420.
Proof.
  intros weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  apply Nat.le_trans with ((4000 * 105 + 500) / 1000).
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
         fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. simpl. lia.
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
    Non-response suggests alternate diagnosis or need for repeat.

    LINKING INVARIANT: The hours_post_dose parameter to assess_response
    corresponds to hours_since_last in DosingState. When assessing response
    at time T after the last dose, use the same T for both:
      assess_response fio2_pre fio2_post T
      DosingState with hours_since_last = T
    This ensures repeat_eligible correctly integrates response assessment. *)
Inductive SurfactantResponse : Type :=
  | Responded        (* FiO2 decreased significantly post-dose *)
  | PartialResponse  (* Some improvement but still elevated FiO2 *)
  | NonResponder.    (* No improvement or worsening *)

(** Response assessment based on FiO2 change.
    Parameter hours_post_dose must equal hours_since_last in DosingState
    for correct integration with repeat_eligible. *)
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

(** Non-responder with adequate interval and elevated FiO2 meets repeat timing. *)
Theorem nonresponder_repeat_timing :
  forall ds fio2_pre fio2_post,
    assess_response fio2_pre fio2_post (hours_since_last ds) = NonResponder ->
    fio2_elevated fio2_post ->
    doses_given ds < max_doses (product ds) ->
    hours_since_last ds >= min_hours_between_doses (product ds) ->
    repeat_eligible ds fio2_post.
Proof.
  intros ds fio2_pre fio2_post _ Hfio2 Hdoses Htiming.
  unfold repeat_eligible. auto.
Qed.

(** Partial responder with elevated FiO2 also meets repeat criteria. *)
Theorem partial_responder_repeat_timing :
  forall ds fio2_pre fio2_post,
    assess_response fio2_pre fio2_post (hours_since_last ds) = PartialResponse ->
    fio2_elevated fio2_post ->
    doses_given ds < max_doses (product ds) ->
    hours_since_last ds >= min_hours_between_doses (product ds) ->
    repeat_eligible ds fio2_post.
Proof.
  intros ds fio2_pre fio2_post _ Hfio2 Hdoses Htiming.
  unfold repeat_eligible. auto.
Qed.

(** Full responder (FiO2 no longer elevated) cannot meet repeat criteria. *)
Theorem responder_no_repeat :
  forall ds fio2_post,
    ~ fio2_elevated fio2_post ->
    ~ repeat_eligible ds fio2_post.
Proof.
  intros ds fio2_post Hnot_elevated.
  unfold repeat_eligible. intros [_ [_ Hfio2]].
  contradiction.
Qed.

(** -------------------------------------------------------------------------- *)
(** Timed Automata Model (UPPAAL)                                              *)
(** -------------------------------------------------------------------------- *)

(** Timed automata locations for surfactant therapy state machine.
    Models the lifecycle from RDS diagnosis through treatment and response. *)
Inductive TALocation : Type :=
  | TA_Initial           (* Pre-diagnosis state *)
  | TA_RDS_Diagnosed     (* RDS diagnosed, clock starts *)
  | TA_Evaluating        (* Evaluating for surfactant *)
  | TA_Surfactant_Given  (* Surfactant administered *)
  | TA_Monitoring        (* Post-dose monitoring *)
  | TA_Responded         (* Good response, weaning *)
  | TA_NonResponder      (* Poor response, consider repeat *)
  | TA_Weaned.           (* Successfully weaned *)

(** Timed automata transitions with timing constraints.
    minutes_elapsed: time since entering current state *)
Record TATransition := mkTATransition {
  ta_from : TALocation;
  ta_to : TALocation;
  ta_guard_min : nat;    (* Minimum time in minutes *)
  ta_guard_max : nat     (* Maximum time in minutes, 0 = no max *)
}.

(** Key timing constraints for surfactant therapy. *)
Definition surfactant_window_max : nat := 120.    (* 2 hours from RDS onset *)
Definition response_eval_min : nat := 120.        (* 2 hours post-dose minimum *)
Definition response_eval_max : nat := 360.        (* 6 hours post-dose maximum *)
Definition repeat_interval_min : nat := 360.      (* 6 hours between doses *)

(** Valid timed automata transitions. *)
Definition valid_ta_transitions : list TATransition :=
  [ mkTATransition TA_Initial TA_RDS_Diagnosed 0 0
  ; mkTATransition TA_RDS_Diagnosed TA_Evaluating 0 surfactant_window_max
  ; mkTATransition TA_Evaluating TA_Surfactant_Given 0 surfactant_window_max
  ; mkTATransition TA_Surfactant_Given TA_Monitoring 0 0
  ; mkTATransition TA_Monitoring TA_Responded response_eval_min response_eval_max
  ; mkTATransition TA_Monitoring TA_NonResponder response_eval_min response_eval_max
  ; mkTATransition TA_NonResponder TA_Surfactant_Given repeat_interval_min 0
  ; mkTATransition TA_Responded TA_Weaned 0 0
  ].

(** -------------------------------------------------------------------------- *)
(** Temporal Assertions                                                        *)
(** -------------------------------------------------------------------------- *)

(** Temporal assertion: surfactant should be given within 2 hours of RDS onset.
    Per European Consensus 2022: early surfactant improves outcomes. *)
Definition surfactant_timing_ok (minutes_since_rds_onset : nat)
                                 (surfactant_given : bool) : Prop :=
  surfactant_given = true -> minutes_since_rds_onset <= surfactant_window_max.

(** Temporal assertion: response evaluation within valid window. *)
Definition response_eval_timing_ok (minutes_since_dose : nat) : Prop :=
  minutes_since_dose >= response_eval_min /\ minutes_since_dose <= response_eval_max.

(** Temporal assertion: repeat dose respects minimum interval. *)
Definition repeat_timing_ok (minutes_since_last_dose : nat) : Prop :=
  minutes_since_last_dose >= repeat_interval_min.

(** --- Witness: 90 minutes is within surfactant window --- *)
Lemma surfactant_at_90min_ok : surfactant_timing_ok 90 true.
Proof.
  unfold surfactant_timing_ok, surfactant_window_max. lia.
Qed.

(** --- Counterexample: 150 minutes exceeds window --- *)
Lemma surfactant_at_150min_late : ~ surfactant_timing_ok 150 true.
Proof.
  unfold surfactant_timing_ok, surfactant_window_max. lia.
Qed.

(** --- Witness: 180 minutes (3 hours) is valid for response eval --- *)
Lemma response_eval_at_180min_ok : response_eval_timing_ok 180.
Proof.
  unfold response_eval_timing_ok, response_eval_min, response_eval_max. lia.
Qed.

(** Early surfactant (within window) is never too late. *)
Theorem early_surfactant_ok : forall t,
  t <= surfactant_window_max -> surfactant_timing_ok t true.
Proof.
  intros t Ht. unfold surfactant_timing_ok. intros _. exact Ht.
Qed.

(** -------------------------------------------------------------------------- *)
(** Response Assessment Intervals                                              *)
(** -------------------------------------------------------------------------- *)

(** Response assessment time points in minutes post-dose. *)
Definition assessment_timepoint_1 : nat := 120.  (* 2 hours *)
Definition assessment_timepoint_2 : nat := 240.  (* 4 hours *)
Definition assessment_timepoint_3 : nat := 360.  (* 6 hours *)

(** Response assessment interval classification. *)
Inductive AssessmentInterval : Type :=
  | TooEarly           (* < 2 hours: unreliable assessment *)
  | FirstWindow        (* 2-4 hours: first assessment window *)
  | SecondWindow       (* 4-6 hours: second assessment window *)
  | Extended.          (* > 6 hours: extended monitoring *)

(** Classify time post-dose into assessment interval. *)
Definition classify_interval (minutes : nat) : AssessmentInterval :=
  if minutes <? assessment_timepoint_1 then TooEarly
  else if minutes <? assessment_timepoint_2 then FirstWindow
  else if minutes <? assessment_timepoint_3 then SecondWindow
  else Extended.

(** --- Witness: 90 minutes is too early --- *)
Lemma interval_90min : classify_interval 90 = TooEarly.
Proof. reflexivity. Qed.

(** --- Witness: 150 minutes is first window --- *)
Lemma interval_150min : classify_interval 150 = FirstWindow.
Proof. reflexivity. Qed.

(** --- Witness: 300 minutes is second window --- *)
Lemma interval_300min : classify_interval 300 = SecondWindow.
Proof. reflexivity. Qed.

(** --- Witness: 400 minutes is extended --- *)
Lemma interval_400min : classify_interval 400 = Extended.
Proof. reflexivity. Qed.

(** Too early assessment is unreliable. *)
Definition assessment_reliable (minutes : nat) : Prop :=
  classify_interval minutes <> TooEarly.

(** Assessment at 2+ hours is reliable. *)
Theorem assessment_reliable_after_2h : forall minutes,
  minutes >= assessment_timepoint_1 -> assessment_reliable minutes.
Proof.
  intros minutes Hmin.
  unfold assessment_reliable, classify_interval, assessment_timepoint_1,
         assessment_timepoint_2, assessment_timepoint_3.
  assert (H: (minutes <? 120) = false) by (apply Nat.ltb_ge; exact Hmin).
  rewrite H.
  destruct (minutes <? 240); destruct (minutes <? 360); congruence.
Qed.

(** Repeat dose timing consistency: repeat interval aligns with assessment window. *)
Theorem repeat_after_assessment : forall minutes,
  minutes >= repeat_interval_min -> assessment_reliable minutes.
Proof.
  intros minutes Hmin.
  apply assessment_reliable_after_2h.
  unfold repeat_interval_min in Hmin. unfold assessment_timepoint_1. lia.
Qed.

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

(** Ready to wean implies FiO2 not elevated (weaning threshold < FiO2 threshold). *)
Theorem wean_implies_fio2_not_elevated :
  forall fio2 spo2 wob,
    ready_to_wean fio2 spo2 wob -> ~ fio2_elevated fio2.
Proof.
  intros fio2 spo2 wob [Hfio2 _].
  unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30,
         weaning_fio2_threshold in *. lia.
Qed.

(** Ready to wean implies no repeat dose eligible. *)
Theorem wean_implies_no_repeat :
  forall ds fio2 spo2 wob,
    ready_to_wean fio2 spo2 wob -> ~ repeat_eligible ds fio2.
Proof.
  intros ds fio2 spo2 wob Hwean.
  apply responder_no_repeat.
  apply wean_implies_fio2_not_elevated with spo2 wob. exact Hwean.
Qed.

(** Ready to wean implies surfactant treatment complete. *)
Inductive TreatmentStatus : Type :=
  | NeedsSurfactant
  | AwaitingResponse
  | ReadyToWean
  | RequiresEscalation.

(** Determine treatment status based on current state. *)
Definition treatment_status (fio2 : fio2_pct) (spo2 : spo2_pct)
                            (wob : bool) (resp : SurfactantResponse) : TreatmentStatus :=
  if andb (fio2 <=? weaning_fio2_threshold)
          (andb (weaning_spo2_low <=? spo2) (andb (spo2 <=? weaning_spo2_high) (negb wob)))
  then ReadyToWean
  else match resp with
       | Responded => AwaitingResponse  (* Still elevated but improving *)
       | PartialResponse => AwaitingResponse
       | NonResponder => RequiresEscalation
       end.

(** Ready to wean yields ReadyToWean status. *)
Lemma ready_to_wean_status :
  forall fio2 spo2 wob resp,
    ready_to_wean fio2 spo2 wob ->
    treatment_status fio2 spo2 wob resp = ReadyToWean.
Proof.
  intros fio2 spo2 wob resp Hwean.
  unfold ready_to_wean, weaning_fio2_threshold, weaning_spo2_low, weaning_spo2_high in Hwean.
  destruct Hwean as [Hfio2 [Hspo2_lo [Hspo2_hi Hwob]]].
  unfold treatment_status, weaning_fio2_threshold, weaning_spo2_low, weaning_spo2_high.
  replace (fio2 <=? 25) with true by (symmetry; apply Nat.leb_le; lia).
  replace (90 <=? spo2) with true by (symmetry; apply Nat.leb_le; lia).
  replace (spo2 <=? 94) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite Hwob. reflexivity.
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

(** Prophylactic pathway: GA < 30+0w, intubated for stabilization,
    within timing window, no contraindications. Per European Consensus 2022.
    Uses conservative 15-minute window (strictest across all products).
    For product-specific timing (e.g., Infasurf allows 30 min), use
    prophylactic_recommendation_for. *)
Definition prophylactic_recommendation (cs : ClinicalState) : Prop :=
  ga_total_days (cs_patient cs) < prophylactic_ga_threshold_days /\
  cs_current_support cs = Intubated /\
  within_prophylactic_window (cs_minutes_since_birth cs) /\
  no_contraindications (cs_contraindications cs).

(** Product-specific prophylactic pathway using product-specific timing.
    Infasurf allows up to 30 minutes; Survanta/Curosurf use 15 minutes. *)
Definition prophylactic_recommendation_for (cs : ClinicalState)
                                           (prod : SurfactantProduct) : Prop :=
  ga_total_days (cs_patient cs) < prophylactic_ga_threshold_days /\
  cs_current_support cs = Intubated /\
  within_prophylactic_window_for prod (cs_minutes_since_birth cs) /\
  no_contraindications (cs_contraindications cs).

(** Product-specific is at least as permissive as conservative default. *)
Lemma conservative_implies_product_prophylactic :
  forall cs prod,
    prophylactic_recommendation cs ->
    prophylactic_recommendation_for cs prod.
Proof.
  intros cs prod [Hga [Hsup [Htime Hcontra]]].
  unfold prophylactic_recommendation_for, within_prophylactic_window_for,
         prophylactic_window_for_product.
  unfold within_prophylactic_window, prophylactic_window_minutes in Htime.
  split. { exact Hga. }
  split. { exact Hsup. }
  split. { destruct prod; simpl;
           apply Nat.le_trans with 15; auto;
           apply Nat.leb_le; reflexivity. }
  exact Hcontra.
Qed.

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
  split. { unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. lia. }
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
    destruct Hgas as [H | H]; apply Nat.ltb_ge in H; discriminate.
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
  - left. unfold prophylactic_recommendation, ga_total_days,
                 prophylactic_ga_threshold_days, prophylactic_ga_threshold_weeks. simpl.
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
    + unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30. lia.
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
    ga_total_days p >= prophylactic_ga_threshold_days ->
    current_fio2 p <= fio2_threshold ->
    ~ surfactant_indicated p signs.
Proof.
  intros p signs Hga Hfio2.
  unfold prophylactic_ga_threshold_days, prophylactic_ga_threshold_weeks in Hga.
  unfold fio2_threshold, fio2_threshold_30 in Hfio2.
  unfold surfactant_indicated. intros [Hpro | Hres].
  - unfold prophylactic_indicated, prophylactic_ga_threshold_days,
           prophylactic_ga_threshold_weeks in Hpro. lia.
  - unfold rescue_indicated in Hres. destruct Hres as [Hfio2_elev _].
    unfold fio2_elevated, fio2_elevated_at, fio2_threshold, fio2_threshold_30 in Hfio2_elev. lia.
Qed.

(** Withholding from well infant does not miss indication. *)
Theorem withhold_well_infant_safe :
  forall p signs c dose,
    ga_total_days p >= prophylactic_ga_threshold_days ->
    current_fio2 p <= fio2_threshold ->
    ~ safe_to_give p signs c dose.
Proof.
  intros p signs c dose Hga Hfio2.
  unfold safe_to_give. intros [_ [Hind _]].
  apply (well_infant_not_indicated p signs Hga Hfio2). exact Hind.
Qed.

(** Dose from calculation is bounded for valid weights.
    With rounding: max weight 3000g * max rate 200mg/kg + 500 / 1000 = 600mg. *)
Theorem calculated_dose_bounded :
  forall prod weight,
    weight <= 3000 ->
    initial_dose prod weight <= 600.
Proof.
  intros prod weight Hmax.
  unfold initial_dose, calculate_dose, initial_dose_per_kg.
  destruct prod.
  - (* Survanta: (weight * 100 + 500) / 1000 <= 300 <= 600 *)
    apply Nat.le_trans with ((3000 * 100 + 500) / 1000).
    + apply Nat.Div0.div_le_mono. lia.
    + apply Nat.leb_le. reflexivity.
  - (* Curosurf: (weight * 200 + 500) / 1000 <= 600 *)
    apply Nat.le_trans with ((3000 * 200 + 500) / 1000).
    + apply Nat.Div0.div_le_mono. lia.
    + apply Nat.leb_le. reflexivity.
  - (* Infasurf: (weight * 105 + 500) / 1000 <= 315 <= 600 *)
    apply Nat.le_trans with ((3000 * 105 + 500) / 1000).
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
Extract Constant Nat.sub => "(fun n m -> max 0 (n - m))".
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
    ga_total_days p <? prophylactic_ga_threshold_days.

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

  (** Calculate volume in mL × 10 for nursing administration.
      Example: 20 = 2.0 mL. Caller divides by 10 for display. *)
  Definition calc_volume_ml_x10 (prod : SurfactantProduct) (dose_mg : nat) : nat :=
    dose_volume_ml_x10 prod dose_mg.

  (** Calculate number of vials needed. *)
  Definition calc_vials_needed (prod : SurfactantProduct) (dose_mg : nat) : nat :=
    vials_needed prod dose_mg.

  (** Check CPAP failure. *)
  Definition cpap_failed_dec (pressure : nat) (fio2 : fio2_pct) : bool :=
    (cpap_min_pressure <=? pressure) && (fio2_threshold <? fio2).

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
    (age_hours p <=? 168) &&
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
    in_range (ga_days p) 0 6 &&
    in_range (birth_weight p) 200 6000 &&
    in_range (age_hours p) 0 168 &&
    in_range (current_fio2 p) 21 100.

  (** Validate BloodGas fields (pH scaled, pCO2, pO2 all reasonable). *)
  Definition validate_blood_gas (bg : BloodGas) : bool :=
    in_range (ph bg) 6800 7800 &&
    in_range (pco2 bg) 10 150 &&
    in_range (po2 bg) 10 500.

  (** Validate CPAPTrialState fields. *)
  Definition validate_cpap_trial (trial : CPAPTrialState) : bool :=
    in_range (cpap_pressure_cmh2o trial) 0 20 &&
    in_range (cpap_duration_minutes trial) 0 10080 &&
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
