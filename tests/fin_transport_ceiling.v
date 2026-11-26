From LeanImport Require Import Lean.

(* The ceiling of the Fin case of the transport pass (README, "Transport of proof arguments across Nat literals"):
   a lemma t = t' between two Fin values only when the value and every closed Nat operand it is computed from (a
   %, at Lean's Nat instance or reached by head reduction, and the operations the Fin case reads), but a divisor,
   are below 65536. The kernel checks such a lemma through the unary literal of the value, with which it
   converts each of t and t' on the unary Nat; on the Rocq 9.2 cut that takes at most a few seconds at
   65535 % 2 ^ 8 and 65535 % 2 ^ 16, and about 12 s at 65535 % 2 ^ 32.

   dumps/lean434/u8.ndjson is exported from dumps/lean434/src/RLI434U8.lean, Lean's own UInt8, UInt16 and Fin
   literals:
   - le_65535 (export line 9094): (65535 : UInt8) is 65535 % 2 ^ 8 = 255, a dividend above its divisor: a lemma;
   - le16_300 (line 9214) and le16_65535 (line 9243): (300 : UInt16), (65535 : UInt16): a lemma each. The src/ of
     the fix's parent refuses le16_300 at the 30 s limit below (ci/build-9.2-cut.sh --revert-fix);
   - le_300 (line 9063, UInt8.ofNatLT 44 _ against (300 : UInt8) = 300 % 2 ^ 8): the pass's first scan passes the
     entry on, since it names UInt8.ofNatLT, whose type ends in UInt8, a record of one relevant field of an
     inductive type, and OfNat.ofNat UInt8: a lemma; fin_300 (line 9874, Fin.ofNat 256 300 against <44, _>): the
     pass runs, but <44, _> is headed by the constructor Fin.mk, not by a constant, so it is no Fin pair. The
     kernel converts it at once;
   - le_65536 (line 9898) and le_65537 (line 9925): (65536 : UInt8) is 65536 % 2 ^ 8 = 0 and (65537 : UInt8) is
     1, small values whose dividend is at the ceiling and just over it: no lemma; the kernel converts each in about
     2 s. A ceiling on the value alone would give both a lemma, and <= in place of < would give le_65536 one.
   dumps/lean434/fin_ceiling.ndjson is dumps/lean434/utf8size_two.ndjson without its last entry, with theorems
   added (its row in dumps/lean434/README.md), each a cast of a proof of v <= UInt32.ofNatLT t _ to v <= d:
   - castq_65535 (line 11842): d = (65535 : UInt32), at the ceiling - 1: a lemma;
   - badmod_127 (line 11928): d = 127 % 2 ^ 32 through a Mod Nat instance that is not Nat.instMod, myMod :=
     Nat.instMod: no % the Fin case reads, and the head reduction takes it through myMod to Nat.mod 127 (2 ^ 32),
     which it reads: a lemma;
   - u32big_127 (line 11991): d = (4294967423 : UInt32) = 4294967423 % 2 ^ 32 = 127, a dividend above the ceiling,
     and castq_65536 (line 12028): d = (65536 : UInt32), at the ceiling: no lemma, and the kernel's own conversion
     takes far longer than the 30 s limit below (more than 300 s for each on the cut). The limit is above the
     lemma check at the ceiling (about 12 s): <= in place of < would give castq_65536 a lemma, and its import
     would complete within it.
   tests/fin_transport_ceiling.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 30.
Redirect "fin_transport_ceiling_u8.log" Lean Import "../dumps/lean434/u8.ndjson".

Check RLI434U8_le16_300.
Check RLI434U8_le16_300__nat_eq_1.
Check RLI434U8_le16_65535__nat_eq_1.
Check RLI434U8_le_65535__nat_eq_1.
Check RLI434U8_le_300__nat_eq_1.
Check RLI434U8_le_300.
Check RLI434U8_fin_300.
Check RLI434U8_le_65536.
Check RLI434U8_le_65537.

Redirect "fin_transport_ceiling_below.log" Lean Import "../dumps/lean434/fin_ceiling.ndjson" 1 11991.

Check RLI434Fin_castq_65535__nat_eq_1.
Check RLI434Fin_badmod_127__nat_eq_1.
Check RLI434Fin_badmod_127.

Redirect "fin_transport_ceiling_above.log" Lean Import "../dumps/lean434/fin_ceiling.ndjson" 11991.

Fail Check RLI434Fin_u32big_127.
Fail Check RLI434Fin_castq_65536.
