From LeanImport Require Import Lean.

(* Large Int literals in a structure's fields, and a proof by rfl that makes the kernel compare -(-x) with x for
   x = -134217728: the entries of dumps/lean434/bigint.ndjson up to RLI434.big_fields (export line 2241). Its
   proofs by decide and omega over Int values from 2^32 on are tests/lean434_bigint_decide.v. *)
Set Lean Error Mode "Fail".
Timeout 20 Lean Import "../dumps/lean434/bigint.ndjson" 1 2241.

Check RLI434_big.
Check RLI434_big_ok.
Check RLI434_big_fields.
