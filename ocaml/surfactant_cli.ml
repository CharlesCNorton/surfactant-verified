(* surfactant_cli.ml - Command-line interface for surfactant decision logic *)
(* Reads JSON from stdin, writes JSON result to stdout *)
(* Usage: echo '{"patient":...}' | ./surfactant_cli.exe *)

open Surfactant_decision
open SurfactantDecision

(* Simple JSON parsing - hand-rolled for minimal dependencies *)

let trim s =
  let len = String.length s in
  let i = ref 0 in
  while !i < len && (s.[!i] = ' ' || s.[!i] = '\n' || s.[!i] = '\r' || s.[!i] = '\t') do
    incr i
  done;
  let j = ref (len - 1) in
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\n' || s.[!j] = '\r' || s.[!j] = '\t') do
    decr j
  done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

(* Extract integer value from "key": value *)
let get_int json key =
  let pattern = "\"" ^ key ^ "\"" in
  try
    let idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let rest = String.sub json (idx + String.length pattern) (String.length json - idx - String.length pattern) in
    (* Skip : and whitespace *)
    let rest = trim rest in
    let rest = if rest.[0] = ':' then String.sub rest 1 (String.length rest - 1) else rest in
    let rest = trim rest in
    (* Parse integer *)
    let buf = Buffer.create 16 in
    let i = ref 0 in
    while !i < String.length rest && rest.[!i] >= '0' && rest.[!i] <= '9' do
      Buffer.add_char buf rest.[!i];
      incr i
    done;
    int_of_string (Buffer.contents buf)
  with _ -> failwith ("Missing or invalid field: " ^ key)

(* Extract boolean value from "key": true/false *)
let get_bool json key =
  let pattern = "\"" ^ key ^ "\"" in
  try
    let idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let rest = String.sub json (idx + String.length pattern) (String.length json - idx - String.length pattern) in
    let rest = trim rest in
    let rest = if rest.[0] = ':' then String.sub rest 1 (String.length rest - 1) else rest in
    let rest = trim rest in
    if String.length rest >= 4 && String.sub rest 0 4 = "true" then true
    else if String.length rest >= 5 && String.sub rest 0 5 = "false" then false
    else failwith ("Invalid boolean for: " ^ key)
  with _ -> false  (* Default to false for missing bools *)

(* Extract object substring between braces *)
let get_object json key =
  let pattern = "\"" ^ key ^ "\"" in
  try
    let idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let rest = String.sub json (idx + String.length pattern) (String.length json - idx - String.length pattern) in
    let rest = trim rest in
    let rest = if rest.[0] = ':' then String.sub rest 1 (String.length rest - 1) else rest in
    let rest = trim rest in
    if rest.[0] <> '{' then failwith ("Expected object for: " ^ key);
    (* Find matching closing brace *)
    let depth = ref 1 in
    let i = ref 1 in
    while !i < String.length rest && !depth > 0 do
      if rest.[!i] = '{' then incr depth
      else if rest.[!i] = '}' then decr depth;
      incr i
    done;
    String.sub rest 0 !i
  with _ -> "{}"

(* Check if key exists and is not null *)
let has_key json key =
  let pattern = "\"" ^ key ^ "\"" in
  try
    let idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let rest = String.sub json (idx + String.length pattern) (String.length json - idx - String.length pattern) in
    let rest = trim rest in
    let rest = if rest.[0] = ':' then String.sub rest 1 (String.length rest - 1) else rest in
    let rest = trim rest in
    not (String.length rest >= 4 && String.sub rest 0 4 = "null")
  with _ -> false

(* Parse patient from JSON *)
let parse_patient json =
  { ga_weeks = get_int json "ga_weeks";
    ga_days = get_int json "ga_days";
    birth_weight = get_int json "weight";
    age_hours = get_int json "age_hours";
    current_fio2 = get_int json "fio2" }

(* Parse RDS signs from JSON *)
let parse_signs json =
  { grunting = get_bool json "grunting";
    retractions = get_bool json "retractions";
    nasal_flaring = get_bool json "nasal_flaring";
    cyanosis_in_room_air = get_bool json "cyanosis" }

(* Parse contraindications from JSON *)
let parse_contraindications json =
  { congenital_diaphragmatic_hernia = get_bool json "cdh";
    lethal_anomaly = get_bool json "lethal_anomaly";
    pulmonary_hypoplasia = get_bool json "pulmonary_hypoplasia";
    active_pulmonary_hemorrhage = get_bool json "pulmonary_hemorrhage";
    pneumothorax_untreated = get_bool json "pneumothorax" }

(* Parse chest X-ray from JSON *)
let parse_cxr json =
  { ground_glass_opacity = get_bool json "ground_glass";
    air_bronchograms = get_bool json "air_bronchograms";
    low_lung_volumes = get_bool json "low_volumes";
    reticulogranular_pattern = get_bool json "reticulogranular" }

(* Parse blood gas from JSON *)
let parse_blood_gas json =
  { ph = get_int json "ph";
    pco2 = get_int json "pco2";
    po2 = get_int json "po2" }

(* Parse CPAP trial from JSON *)
let parse_cpap json =
  { cpap_pressure_cmh2o = get_int json "pressure";
    cpap_duration_minutes = get_int json "duration";
    fio2_on_cpap = get_int json "fio2" }

(* Parse respiratory support from JSON *)
let parse_support json =
  let s = try
    let pattern = "\"support\"" in
    let idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let rest = String.sub json (idx + String.length pattern) (String.length json - idx - String.length pattern) in
    let rest = trim rest in
    let rest = if rest.[0] = ':' then String.sub rest 1 (String.length rest - 1) else rest in
    trim rest
  with _ -> "\"room_air\""
  in
  if String.length s > 0 && s.[0] = '"' then
    let s = String.sub s 1 (String.length s - 1) in
    let idx = try String.index s '"' with _ -> String.length s in
    let s = String.sub s 0 idx in
    match String.lowercase_ascii s with
    | "cpap" -> CPAP
    | "intubated" -> Intubated
    | _ -> RoomAir
  else RoomAir

(* Parse product from JSON *)
let parse_product json =
  let s = try
    let pattern = "\"product\"" in
    let idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let rest = String.sub json (idx + String.length pattern) (String.length json - idx - String.length pattern) in
    let rest = trim rest in
    let rest = if rest.[0] = ':' then String.sub rest 1 (String.length rest - 1) else rest in
    trim rest
  with _ -> "\"curosurf\""
  in
  if String.length s > 0 && s.[0] = '"' then
    let s = String.sub s 1 (String.length s - 1) in
    let idx = try String.index s '"' with _ -> String.length s in
    let s = String.sub s 0 idx in
    match String.lowercase_ascii s with
    | "survanta" -> Survanta
    | "infasurf" -> Infasurf
    | _ -> Curosurf
  else Curosurf

(* Parse clinical state from JSON *)
let parse_clinical_state json =
  let patient_json = get_object json "patient" in
  let signs_json = get_object json "signs" in
  let contras_json = get_object json "contraindications" in
  let gas_json = get_object json "blood_gas" in

  let imaging =
    if has_key json "cxr" then
      let cxr_json = get_object json "cxr" in
      { ie_cxr = Some (parse_cxr cxr_json);
        ie_ultrasound = None;
        ie_clinical_judgement = get_bool json "clinical_judgement" }
    else
      { ie_cxr = None;
        ie_ultrasound = None;
        ie_clinical_judgement = get_bool json "clinical_judgement" }
  in

  let cpap =
    if has_key json "cpap_trial" then
      Some (parse_cpap (get_object json "cpap_trial"))
    else
      None
  in

  { cs_patient = parse_patient patient_json;
    cs_signs = parse_signs signs_json;
    cs_contraindications = parse_contraindications contras_json;
    cs_imaging = imaging;
    cs_blood_gas = parse_blood_gas gas_json;
    cs_minutes_since_birth = get_int json "minutes_since_birth";
    cs_cpap_trial = cpap;
    cs_current_support = parse_support json }

(* Result to JSON string *)
let result_to_string = function
  | InvalidInput -> "InvalidInput"
  | InvalidPatient -> "InvalidPatient"
  | NotIndicated -> "NotIndicated"
  | Indicated -> "Indicated"

(* Product to string *)
let product_to_string = function
  | Survanta -> "Survanta"
  | Curosurf -> "Curosurf"
  | Infasurf -> "Infasurf"

(* Generate JSON response *)
let make_response result product weight =
  let dose = calc_initial_dose product weight in
  Printf.sprintf
    "{\"result\": \"%s\", \"product\": \"%s\", \"dose_mg\": %d, \"weight_g\": %d}"
    (result_to_string result)
    (product_to_string product)
    dose
    weight

(* Main *)
let () =
  (* Read all of stdin *)
  let buf = Buffer.create 4096 in
  try
    while true do
      Buffer.add_string buf (input_line stdin);
      Buffer.add_char buf '\n'
    done
  with End_of_file -> ();

  let json = Buffer.contents buf in

  try
    let cs = parse_clinical_state json in
    let product = parse_product json in
    let result = recommend_surfactant_safe cs in
    let response = make_response result product cs.cs_patient.birth_weight in
    print_endline response
  with e ->
    Printf.printf "{\"error\": \"%s\"}\n" (Printexc.to_string e)
