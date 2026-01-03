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
