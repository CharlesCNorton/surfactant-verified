
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



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

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val tail_add : int -> int -> int **)

let rec tail_add n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n0 -> tail_add n0 (succ m))
    n

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun n0 -> tail_addmul (tail_add m r) n0 m)
    n

(** val tail_mul : int -> int -> int **)

let tail_mul n m =
  tail_addmul 0 n m

(** val of_uint_acc : uint -> int -> int **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))) acc))))))))))

(** val of_uint : uint -> int **)

let of_uint d =
  of_uint_acc d 0

(** val of_hex_uint_acc : uint0 -> int -> int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ
      (tail_mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ 0)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> int **)

let of_hex_uint d =
  of_hex_uint_acc d 0

(** val of_num_uint : uint1 -> int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

module Nat =
 struct
  (** val leb : int -> int -> bool **)

  let rec leb = (<=)

  (** val ltb : int -> int -> bool **)

  let ltb = (<)

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n = 0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = (/)
 end

type gestational_age = int

type ga_days_t = int

type weight_g = int

type postnatal_hours = int

type fio2_pct = int

type patient = { ga_weeks : gestational_age; ga_days : ga_days_t;
                 birth_weight : weight_g; age_hours : postnatal_hours;
                 current_fio2 : fio2_pct }

(** val ga_total_days : patient -> int **)

let ga_total_days p =
  add (mul p.ga_weeks (succ (succ (succ (succ (succ (succ (succ 0))))))))
    p.ga_days

(** val prophylactic_ga_threshold_weeks : int **)

let prophylactic_ga_threshold_weeks =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ 0)))))))))))))))))))))))))))))

(** val prophylactic_ga_threshold_days : int **)

let prophylactic_ga_threshold_days =
  mul prophylactic_ga_threshold_weeks (succ (succ (succ (succ (succ (succ
    (succ 0)))))))

type rDSSigns = { grunting : bool; retractions : bool; nasal_flaring : 
                  bool; cyanosis_in_room_air : bool }

(** val sign_count : rDSSigns -> int **)

let sign_count s =
  add
    (add
      (add (if s.grunting then succ 0 else 0)
        (if s.retractions then succ 0 else 0))
      (if s.nasal_flaring then succ 0 else 0))
    (if s.cyanosis_in_room_air then succ 0 else 0)

type contraindications = { congenital_diaphragmatic_hernia : bool;
                           lethal_anomaly : bool;
                           pulmonary_hypoplasia : bool;
                           active_pulmonary_hemorrhage : bool;
                           pneumothorax_untreated : bool }

(** val fio2_threshold_30 : int **)

let fio2_threshold_30 =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ 0)))))))))))))))))))))))))))))

(** val fio2_threshold : int **)

let fio2_threshold =
  fio2_threshold_30

type respiratorySupport =
| RoomAir
| CPAP
| Intubated

type cPAPTrialState = { cpap_pressure_cmh2o : int;
                        cpap_duration_minutes : int; fio2_on_cpap : fio2_pct }

(** val cpap_min_pressure : int **)

let cpap_min_pressure =
  succ (succ (succ (succ (succ (succ 0)))))

type ph_scaled = int

type pco2_mmhg = int

type bloodGas = { ph : ph_scaled; pco2 : pco2_mmhg; po2 : int }

(** val ph_critical_low : int **)

let ph_critical_low =
  of_num_uint (UIntDecimal (D7 (D2 (D0 (D0 Nil)))))

(** val pco2_critical_high : int **)

let pco2_critical_high =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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

(** val prophylactic_window_minutes : int **)

let prophylactic_window_minutes =
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ 0))))))))))))))

type surfactantProduct =
| Survanta
| Curosurf
| Infasurf

(** val initial_dose_per_kg : surfactantProduct -> int **)

let initial_dose_per_kg = function
| Survanta ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Curosurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Infasurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val repeat_dose_per_kg : surfactantProduct -> int **)

let repeat_dose_per_kg = function
| Infasurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| _ ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val calculate_dose : int -> int -> int **)

let calculate_dose weight_g0 dose_per_kg =
  Nat.div
    (add (mul weight_g0 dose_per_kg) (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val initial_dose : surfactantProduct -> weight_g -> int **)

let initial_dose prod0 weight =
  calculate_dose weight (initial_dose_per_kg prod0)

(** val repeat_dose : surfactantProduct -> weight_g -> int **)

let repeat_dose prod0 weight =
  calculate_dose weight (repeat_dose_per_kg prod0)

(** val concentration_mg_per_ml : surfactantProduct -> int **)

let concentration_mg_per_ml = function
| Survanta ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ 0))))))))))))))))))))))))
| Curosurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Infasurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))

(** val max_vial_mg : surfactantProduct -> int **)

let max_vial_mg = function
| Survanta ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Curosurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Infasurf ->
  succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val dose_volume_ml_x10 : surfactantProduct -> int -> int **)

let dose_volume_ml_x10 prod0 dose_mg =
  Nat.div
    (mul dose_mg (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      0))))))))))) (concentration_mg_per_ml prod0)

(** val vials_needed : surfactantProduct -> int -> int **)

let vials_needed prod0 dose_mg =
  Nat.div (sub (add dose_mg (max_vial_mg prod0)) (succ 0)) (max_vial_mg prod0)

type clinicalState = { cs_patient : patient; cs_signs : rDSSigns;
                       cs_contraindications : contraindications;
                       cs_imaging : imagingEvidence; cs_blood_gas : bloodGas;
                       cs_minutes_since_birth : minutes_since_birth;
                       cs_cpap_trial : cPAPTrialState option;
                       cs_current_support : respiratorySupport }

module SurfactantDecision =
 struct
  (** val sign_count_dec : rDSSigns -> int **)

  let sign_count_dec =
    sign_count

  (** val fio2_elevated_dec : fio2_pct -> bool **)

  let fio2_elevated_dec f =
    Nat.ltb fio2_threshold f

  (** val prophylactic_indicated_dec : patient -> bool **)

  let prophylactic_indicated_dec p =
    Nat.ltb (ga_total_days p) prophylactic_ga_threshold_days

  (** val clinical_rds_dec : rDSSigns -> bool **)

  let clinical_rds_dec s =
    Nat.leb (succ (succ 0)) (sign_count s)

  (** val calc_initial_dose : surfactantProduct -> weight_g -> int **)

  let calc_initial_dose =
    initial_dose

  (** val calc_repeat_dose : surfactantProduct -> weight_g -> int **)

  let calc_repeat_dose =
    repeat_dose

  (** val calc_volume_ml_x10 : surfactantProduct -> int -> int **)

  let calc_volume_ml_x10 =
    dose_volume_ml_x10

  (** val calc_vials_needed : surfactantProduct -> int -> int **)

  let calc_vials_needed =
    vials_needed

  (** val cpap_failed_dec : int -> fio2_pct -> bool **)

  let cpap_failed_dec pressure fio2 =
    (&&) (Nat.leb cpap_min_pressure pressure) (Nat.ltb fio2_threshold fio2)

  (** val acidosis_dec : ph_scaled -> pco2_mmhg -> bool **)

  let acidosis_dec ph_val pco2_val =
    (||) (Nat.ltb ph_val ph_critical_low)
      (Nat.ltb pco2_critical_high pco2_val)

  (** val no_contraindications_dec : contraindications -> bool **)

  let no_contraindications_dec c =
    (&&)
      ((&&)
        ((&&)
          ((&&) (negb c.congenital_diaphragmatic_hernia)
            (negb c.lethal_anomaly)) (negb c.pulmonary_hypoplasia))
        (negb c.active_pulmonary_hemorrhage)) (negb c.pneumothorax_untreated)

  (** val cxr_consistent_dec : chestXRay -> bool **)

  let cxr_consistent_dec cxr =
    (||) cxr.ground_glass_opacity
      ((&&) cxr.air_bronchograms cxr.low_lung_volumes)

  (** val ultrasound_consistent_dec : lungUltrasound -> bool **)

  let ultrasound_consistent_dec us =
    (||) us.bilateral_white_lung
      ((&&) us.consolidations us.pleural_irregularity)

  (** val imaging_supports_dec : imagingEvidence -> bool **)

  let imaging_supports_dec ie =
    (||)
      ((||)
        (match ie.ie_cxr with
         | Some cxr -> cxr_consistent_dec cxr
         | None -> false)
        (match ie.ie_ultrasound with
         | Some us -> ultrasound_consistent_dec us
         | None -> false)) ie.ie_clinical_judgement

  (** val within_timing_window_dec : minutes_since_birth -> bool **)

  let within_timing_window_dec mins =
    Nat.leb mins prophylactic_window_minutes

  (** val valid_patient_dec : patient -> bool **)

  let valid_patient_dec p =
    (&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  (Nat.leb (succ (succ (succ (succ (succ (succ (succ (succ
                    (succ (succ (succ (succ (succ (succ (succ (succ (succ
                    (succ (succ (succ (succ (succ 0))))))))))))))))))))))
                    p.ga_weeks)
                  (Nat.leb p.ga_weeks (succ (succ (succ (succ (succ (succ
                    (succ (succ (succ (succ (succ (succ (succ (succ (succ
                    (succ (succ (succ (succ (succ (succ (succ (succ (succ
                    (succ (succ (succ (succ (succ (succ (succ (succ (succ
                    (succ (succ (succ (succ (succ (succ (succ (succ (succ
                    0))))))))))))))))))))))))))))))))))))))))))))
                (Nat.leb p.ga_days (succ (succ (succ (succ (succ (succ
                  0))))))))
              (Nat.leb (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ
                0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                p.birth_weight))
            (Nat.leb p.birth_weight
              (of_num_uint (UIntDecimal (D6 (D0 (D0 (D0 Nil))))))))
          (Nat.leb p.age_hours (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (Nat.leb (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          0))))))))))))))))))))) p.current_fio2))
      (Nat.leb p.current_fio2 (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val surfactant_indicated_dec : patient -> rDSSigns -> bool **)

  let surfactant_indicated_dec p signs =
    (||) (prophylactic_indicated_dec p)
      ((&&) (fio2_elevated_dec p.current_fio2) (clinical_rds_dec signs))

  (** val prophylactic_rec_dec :
      patient -> respiratorySupport -> minutes_since_birth ->
      contraindications -> bool **)

  let prophylactic_rec_dec p support mins c =
    (&&)
      ((&&)
        ((&&) (prophylactic_indicated_dec p)
          (match support with
           | Intubated -> true
           | _ -> false)) (within_timing_window_dec mins))
      (no_contraindications_dec c)

  (** val blood_gas_supports_dec : bloodGas -> bool **)

  let blood_gas_supports_dec bg =
    (||) (Nat.ltb bg.ph ph_critical_low) (Nat.ltb pco2_critical_high bg.pco2)

  (** val rescue_rec_dec :
      fio2_pct -> rDSSigns -> imagingEvidence -> bloodGas ->
      contraindications -> respiratorySupport -> cPAPTrialState option -> bool **)

  let rescue_rec_dec fio2 signs imaging bg c support cpap_trial =
    (&&)
      ((&&)
        ((&&) ((&&) (fio2_elevated_dec fio2) (clinical_rds_dec signs))
          ((||) (imaging_supports_dec imaging) (blood_gas_supports_dec bg)))
        (no_contraindications_dec c))
      (match support with
       | RoomAir -> false
       | CPAP ->
         (match cpap_trial with
          | Some trial ->
            cpap_failed_dec trial.cpap_pressure_cmh2o trial.fio2_on_cpap
          | None -> false)
       | Intubated -> true)

  (** val recommend_surfactant : clinicalState -> bool **)

  let recommend_surfactant cs =
    (&&) (valid_patient_dec cs.cs_patient)
      ((||)
        (prophylactic_rec_dec cs.cs_patient cs.cs_current_support
          cs.cs_minutes_since_birth cs.cs_contraindications)
        (rescue_rec_dec cs.cs_patient.current_fio2 cs.cs_signs cs.cs_imaging
          cs.cs_blood_gas cs.cs_contraindications cs.cs_current_support
          cs.cs_cpap_trial))

  (** val in_range : int -> int -> int -> bool **)

  let in_range n min max =
    (&&) (Nat.leb min n) (Nat.leb n max)

  (** val validate_patient : patient -> bool **)

  let validate_patient p =
    (&&)
      ((&&)
        ((&&)
          ((&&)
            (in_range p.ga_weeks (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ 0)))))))))))))))))))))) (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ 0)))))))))))))))))))))))))))))))))))))))))))
            (in_range p.ga_days 0 (succ (succ (succ (succ (succ (succ 0))))))))
          (in_range p.birth_weight (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (of_num_uint (UIntDecimal (D6 (D0 (D0 (D0 Nil))))))))
        (in_range p.age_hours 0 (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (in_range p.current_fio2 (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ 0))))))))))))))))))))) (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val validate_blood_gas : bloodGas -> bool **)

  let validate_blood_gas bg =
    (&&)
      ((&&)
        (in_range bg.ph (of_num_uint (UIntDecimal (D6 (D8 (D0 (D0 Nil))))))
          (of_num_uint (UIntDecimal (D7 (D8 (D0 (D0 Nil)))))))
        (in_range bg.pco2 (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ 0)))))))))) (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (in_range bg.po2 (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ 0)))))))))) (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val validate_cpap_trial : cPAPTrialState -> bool **)

  let validate_cpap_trial trial =
    (&&)
      ((&&)
        (in_range trial.cpap_pressure_cmh2o 0 (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ 0)))))))))))))))))))))
        (in_range trial.cpap_duration_minutes 0
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D8 (D0 Nil)))))))))
      (in_range trial.fio2_on_cpap (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ 0))))))))))))))))))))) (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
        (succ (succ (succ (succ (succ (succ (succ (succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val validate_clinical_state : clinicalState -> bool **)

  let validate_clinical_state cs =
    (&&)
      ((&&)
        ((&&) (validate_patient cs.cs_patient)
          (validate_blood_gas cs.cs_blood_gas))
        (in_range cs.cs_minutes_since_birth 0
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D8 (D0 Nil)))))))))
      (match cs.cs_cpap_trial with
       | Some trial -> validate_cpap_trial trial
       | None -> true)

  type coq_RecommendationResult =
  | InvalidInput
  | InvalidPatient
  | NotIndicated
  | Indicated

  (** val coq_RecommendationResult_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_RecommendationResult -> 'a1 **)

  let coq_RecommendationResult_rect f f0 f1 f2 = function
  | InvalidInput -> f
  | InvalidPatient -> f0
  | NotIndicated -> f1
  | Indicated -> f2

  (** val coq_RecommendationResult_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_RecommendationResult -> 'a1 **)

  let coq_RecommendationResult_rec f f0 f1 f2 = function
  | InvalidInput -> f
  | InvalidPatient -> f0
  | NotIndicated -> f1
  | Indicated -> f2

  (** val recommend_surfactant_safe :
      clinicalState -> coq_RecommendationResult **)

  let recommend_surfactant_safe cs =
    if negb (validate_clinical_state cs)
    then InvalidInput
    else if negb (valid_patient_dec cs.cs_patient)
         then InvalidPatient
         else if recommend_surfactant cs then Indicated else NotIndicated
 end
