
val negb : bool -> bool



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

module Nat :
 sig
  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int
 end

type gestational_age = int

type ga_days_t = int

type weight_g = int

type postnatal_hours = int

type fio2_pct = int

type patient = { ga_weeks : gestational_age; ga_days : ga_days_t;
                 birth_weight : weight_g; age_hours : postnatal_hours;
                 current_fio2 : fio2_pct }

val ga_total_days : patient -> int

val prophylactic_ga_threshold_weeks : int

val prophylactic_ga_threshold_days : int

type rDSSigns = { grunting : bool; retractions : bool; nasal_flaring : 
                  bool; cyanosis_in_room_air : bool }

val sign_count : rDSSigns -> int

type contraindications = { congenital_diaphragmatic_hernia : bool;
                           lethal_anomaly : bool;
                           pulmonary_hypoplasia : bool;
                           active_pulmonary_hemorrhage : bool;
                           pneumothorax_untreated : bool }

val fio2_threshold_30 : int

val fio2_threshold : int

type respiratorySupport =
| RoomAir
| CPAP
| Intubated

type cPAPTrialState = { cpap_pressure_cmh2o : int;
                        cpap_duration_minutes : int; fio2_on_cpap : fio2_pct }

val cpap_min_pressure : int

val cpap_min_duration_minutes : int

type ph_scaled = int

type pco2_mmhg = int

type bloodGas = { ph : ph_scaled; pco2 : pco2_mmhg; po2 : int }

val ph_critical_low : int

val pco2_critical_high : int

type chestXRay = { ground_glass_opacity : bool; air_bronchograms : bool;
                   low_lung_volumes : bool; reticulogranular_pattern : 
                   bool }

type lungUltrasound = { bilateral_white_lung : bool; absent_a_lines : 
                        bool; pleural_irregularity : bool;
                        consolidations : bool }

type imagingEvidence = { ie_cxr : chestXRay option;
                         ie_ultrasound : lungUltrasound option;
                         ie_clinical_judgement : bool }

type minutes_since_birth = int

val prophylactic_window_minutes : int

type surfactantProduct =
| Survanta
| Curosurf
| Infasurf

val initial_dose_per_kg : surfactantProduct -> int

val repeat_dose_per_kg : surfactantProduct -> int

val calculate_dose : int -> int -> int

val initial_dose : surfactantProduct -> weight_g -> int

val repeat_dose : surfactantProduct -> weight_g -> int

val concentration_mg_per_ml : surfactantProduct -> int

val max_vial_mg : surfactantProduct -> int

val dose_volume_ml_x10 : surfactantProduct -> int -> int

val vials_needed : surfactantProduct -> int -> int

type clinicalState = { cs_patient : patient; cs_signs : rDSSigns;
                       cs_contraindications : contraindications;
                       cs_imaging : imagingEvidence; cs_blood_gas : bloodGas;
                       cs_minutes_since_birth : minutes_since_birth;
                       cs_cpap_trial : cPAPTrialState option;
                       cs_current_support : respiratorySupport }

module SurfactantDecision :
 sig
  val sign_count_dec : rDSSigns -> int

  val fio2_elevated_dec : fio2_pct -> bool

  val prophylactic_indicated_dec : patient -> bool

  val clinical_rds_dec : rDSSigns -> bool

  val calc_initial_dose : surfactantProduct -> weight_g -> int

  val calc_repeat_dose : surfactantProduct -> weight_g -> int

  val calc_volume_ml_x10 : surfactantProduct -> int -> int

  val calc_vials_needed : surfactantProduct -> int -> int

  val cpap_failed_dec : int -> fio2_pct -> bool

  val cpap_duration_sufficient_at_dec : int -> cPAPTrialState -> bool

  val cpap_duration_sufficient_dec : cPAPTrialState -> bool

  val cpap_failed_with_duration_at_dec : int -> cPAPTrialState -> bool

  val acidosis_dec : ph_scaled -> pco2_mmhg -> bool

  val no_contraindications_dec : contraindications -> bool

  val cxr_consistent_dec : chestXRay -> bool

  val ultrasound_consistent_dec : lungUltrasound -> bool

  val imaging_supports_dec : imagingEvidence -> bool

  val within_timing_window_dec : minutes_since_birth -> bool

  val valid_patient_dec : patient -> bool

  val surfactant_indicated_dec : patient -> rDSSigns -> bool

  val prophylactic_rec_dec :
    patient -> respiratorySupport -> minutes_since_birth -> contraindications
    -> bool

  val blood_gas_supports_dec : bloodGas -> bool

  val rescue_rec_dec :
    fio2_pct -> rDSSigns -> imagingEvidence -> bloodGas -> contraindications
    -> respiratorySupport -> cPAPTrialState option -> bool

  val recommend_surfactant : clinicalState -> bool

  val in_range : int -> int -> int -> bool

  val validate_patient : patient -> bool

  val validate_blood_gas : bloodGas -> bool

  val validate_cpap_trial : cPAPTrialState -> bool

  val validate_clinical_state : clinicalState -> bool

  type coq_RecommendationResult =
  | InvalidInput
  | InvalidPatient
  | NotIndicated
  | Indicated

  val coq_RecommendationResult_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_RecommendationResult -> 'a1

  val coq_RecommendationResult_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_RecommendationResult -> 'a1

  val recommend_surfactant_safe : clinicalState -> coq_RecommendationResult
 end
