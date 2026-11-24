From LeanImport Require Import Lean ULiftCumulativeRegistration.

Set Lean Error Mode "Skip".

(* P2, P3, P9: only the last entry in each fixture differs. *)
(* predeclared member: Eq *)
Redirect "predeclared_eq.log" Succeed Lean Import "../dumps/lean434/pred_eq.ndjson".
(* predeclared member: Nat *)
Redirect "predeclared_nat.log" Succeed Lean Import "../dumps/lean434/pred_nat.ndjson".
(* predeclared member: Nat.le *)
Redirect "predeclared_nat_le.log" Succeed Lean Import "../dumps/lean434/pred_nat_le.ndjson".
(* predeclared member: Or *)
Redirect "predeclared_or.log" Succeed Lean Import "../dumps/lean434/pred_or.ndjson".
(* predeclared member: And *)
Redirect "predeclared_and.log" Succeed Lean Import "../dumps/lean434/pred_and.ndjson".
(* predeclared member: Fin *)
Redirect "predeclared_fin.log" Succeed Lean Import "../dumps/lean434/pred_fin.ndjson".
(* predeclared member: UInt32 *)
Redirect "predeclared_uint32.log" Succeed Lean Import "../dumps/lean434/pred_uint32.ndjson".
(* predeclared member: BitVec *)
Redirect "predeclared_bitvec.log" Succeed Lean Import "../dumps/lean434/pred_bitvec.ndjson".
(* predeclared member: Char *)
Redirect "predeclared_char.log" Succeed Lean Import "../dumps/lean434/pred_char.ndjson".
(* predeclared member: ULift *)
Redirect "predeclared_ulift.log" Succeed Lean Import "../dumps/lean434/pred_ulift.ndjson".
(* predeclared member: UInt32.size *)
Redirect "predeclared_uint32_size.log" Succeed Lean Import "../dumps/lean434/pred_uint32_size.ndjson".
(* predeclared member: Nat.isValidChar *)
Redirect "predeclared_nat_isvalidchar.log" Succeed Lean Import "../dumps/lean434/pred_nat_isvalidchar.ndjson".
(* predeclared member: Nat.pow *)
Redirect "predeclared_nat_pow.log" Succeed Lean Import "../dumps/lean434/pred_nat_pow.ndjson".

(* P8: importing another export does not declare extra registrations. *)
Redirect "predeclared_absent.log" Succeed Lean Import "../dumps/lean434/parse_empty.ndjson".

(* P10: a repeated UInt32 entry does not overwrite the first one. *)
Redirect "predeclared_duplicate.log" Succeed Lean Import "../dumps/lean434/pred_duplicate.ndjson".

(* P4, P5: locate the export declarations rather than registered values. *)
Set Lean Error Mode "Fail".
Redirect "predeclared_new.log" Lean Import "../dumps/lean434/predeclared.ndjson".
Redirect "predeclared_locate_BitVec.log" Locate BitVec.
Redirect "predeclared_locate_UInt32.log" Locate UInt32.
Redirect "predeclared_locate_Char.log" Locate Char.
Redirect "predeclared_locate_UInt32_size.log" Locate UInt32_size.
Redirect "predeclared_locate_Nat_isValidChar.log" Locate Nat_isValidChar.
Redirect "predeclared_locate_Nat_pow.log" Locate Nat_pow.
Redirect "predeclared_locate_Nat_add.log" Locate Nat_add.
Redirect "predeclared_locate_Nat_mul.log" Locate Nat_mul.

(* P1: lean434_pow.v and lean434_bitvec_uint32.v check the equations
   and the constructor/field uses. P6 and P7 retain the old suite. *)
