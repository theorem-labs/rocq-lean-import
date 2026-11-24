From LeanImport Require Import Lean.

(* The transport of SProp arguments across Nat literals (README, "Transport of proof arguments across Nat
   literals"). tests/nat_transport.expect checks the logs: each entry whose value the pass changes has a
   line "line N: NAME: <k> argument(s) transported (<lemmas>)". *)
Set Lean Error Mode "Fail".

(* W4: dumps/lean434/char_size_2pow31.ndjson is char.ndjson with UInt32.size := 2147483648. Char.ofNatAux
   passes a proof of n < UInt32.size where BitVec.ofNatLT expects n < 2 ^ 32: the values differ, no lemma is
   generated, and the kernel refuses the entry (the unary comparison overflows the stack or runs into the
   Lean Entry Timeout). *)
Set Lean Entry Timeout 20.
Redirect "nat_transport_size.log" Fail Lean Import "../dumps/lean434/char_size_2pow31.ndjson".
(* W4: dumps/lean434/char_pow_zero.ndjson is char.ndjson with Nat.pow m n := Nat.zero. The value finder
   reads 2 ^ 32 by the name Nat.pow and finds it equal to UInt32.size; the lemma it generates states
   Nat.pow b 0 = 1 by Logic.eq_refl, the kernel refuses it, and Char.ofNatAux is refused as without the
   transport. *)
Redirect "nat_transport_pow.log" Fail Lean Import "../dumps/lean434/char_pow_zero.ndjson".
Unset Lean Entry Timeout.

(* W1: Char.ofNatAux is transported and imported, and Char.ofNat after it. *)
Redirect "nat_transport_char.log" Lean Import "../dumps/lean434/char.ndjson".
Check Char_ofNatAux.
Check Char_ofNat.
(* The generated lemma Char.ofNatAux uses, and what it relies on. An axiom would print as "name : type"; the
   definitional UIP of Lean's eq (src/Lean.v) prints as "eq relies on definitional UIP.", as for every entry
   that names eq. *)
Check Char_ofNatAux__nat_eq_1.
Redirect "nat_transport_assumptions_lemma.log" Print Assumptions Char_ofNatAux__nat_eq_1.
(* The lemmas of src/Lean.v on toN rely on nothing; Nat_eq_of_toN and sprop_transport only on that UIP. *)
Definition nat_transport_toN_lemmas : unit :=
  let _ := @toN_inj in let _ := @toN_double in let _ := @toN_add in let _ := @toN_mul in
  let _ := @toN_pow in let _ := @toN_succ_step in let _ := @toN_double_step in
  let _ := @toN_unfold_step in let _ := @toN_op_step in tt.
Redirect "nat_transport_assumptions_toN.log" Print Assumptions nat_transport_toN_lemmas.
Definition nat_transport_eq_lemmas : unit := let _ := @Nat_eq_of_toN in let _ := @sprop_transport in tt.
Redirect "nat_transport_assumptions_eq.log" Print Assumptions nat_transport_eq_lemmas.
(* The value of Char.ofNatAux holds the cast; W5: Char.ofNat's own value, which the pass leaves alone, does
   not. *)
Redirect "nat_transport_print_aux.log" Print Char_ofNatAux.
Redirect "nat_transport_print_ofnat.log" Print Char_ofNat.

(* W2, W3: dumps/lean434/uint32_transport.ndjson. Its entries already imported from char.ndjson above are
   skipped as duplicates, and the lemma Char.ofNatAux generated for UInt32.size = 2 ^ 32 is reused. *)
Redirect "nat_transport_uint32.log" Lean Import "../dumps/lean434/uint32_transport.ndjson".
Check UInt32_ofNatLT.
Check UInt32_toNat_shiftLeft.
Check UInt32_toNat_ofNatLT.
(* W3: the data of UInt32.ofNatLT is Lean's: its toNat is n by conversion. *)
Check (fun (n : Nat) h => eq_refl n : eq (UInt32_toNat (UInt32_ofNatLT n h)) n).
