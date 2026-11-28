From LeanImport Require Import Lean.

(* The bitwise Fin case of the transport pass (README, "Transport of proof arguments across Nat literals"): the
   Fin values read through Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, Nat.sub and Nat.div, and
   through a head reduction to a form the reader reads; parameters and bounds compared by value; the Fin lemma
   through the unary literal of the value; and the first scan's data records. dumps/lean434/bitwise.ndjson is
   exported from dumps/lean434/src/RLI434Bitwise.lean. Most theorems pass a proof of v <= UInt8.ofNatLT k _ where
   v <= UInt8.ofNat e is expected, whose Fin pair is k against e % 2 ^ 8; a W pair is W.ofA p 127 _ against
   W.ofB q 127, W n a record of one field over Fin 256 with the Nat parameter n.
   Cast (a lemma on the two Fin values):
   - and_224 (export line 15279): v = 128 against v = (224 : UInt8) &&& 128 at the instance myAnd8, of the
     parseFirstByte roots' Fin value BitVec.toNat (UInt8.toBitVec 224) &&& BitVec.toNat (UInt8.toBitVec 128): the
     first scan passes it on at OfNat.ofNat UInt8, the head reduction takes each operand to 224 % 2 ^ 8 and
     128 % 2 ^ 8, and the lemma goes through the unary literal 128. The src/ of the fix's parent skips the entry
     and the kernel converts Lean's value within the 10 s limit; and_224_again (16160): the same two terms, which
     reuse and_224's lemma;
   - u32_and (15648) and u32_lor (15810): UInt32.ofNat (255 &&& 127) and UInt32.ofNat (255 ||| 0). The src/ of the
     fix's parent reads no Fin value of either and refuses u32_and at the 10 s limit (ci/build-9.2-cut.sh
     --revert-fix): Rocq's kernel converts a UInt32 value through 2 ^ 32 on the unary Nat;
   - land_fun (15875), land_class (15881): Nat.land 255 127 and 255 &&& 127; lor_class (15904): 255 ||| 127;
     xor_both (16158): 255 ^^^ 15 = 240;
   - width_8 (16201) and width_8b (16216): v = BitVec.ofNat (2 + 6) 128 and BitVec.ofNat (1 + 7) 128 against
     v = (128 : BitVec 8), the widths of the isInvalidContinuationByte and parseFirstByte_eq_done roots: the
     widths and the bounds 2 ^ (2 + 6) and 2 ^ 8 compare equal by value;
   - land_myinst (16229): 255 &&& 127 at myAnd := Nat.instAndOp, which the head reduction takes to
     Nat.land 255 127;
   - sub_127 (16271): 200 - 73; sub_trunc (16299): 5 - 7 = 0; div_127 (16311): 254 / 2; div_zero (16319): 127 / 0
     = 0; shl_6 (16511): 3 <<< 6 = 192; shl_15 (16519): 1 <<< 15 = 32768, of value 0 % 2 ^ 8 (the unary literal
     is Nat_zero); shl_zero (16538): 0 <<< 17 = 0;
   - natrow_add (16598): (255 &&& 127) + 0, and natrow_succ (16611): Nat.succ (BitVec.toNat (UInt8.toBitVec 126)),
     a Nat form over an operand only a row or the head reduction reads; succ_head (16624): id (Nat.succ 126);
   - fb_63 (16991) and fb_64 (17002): a head reduction of 63 and 64 steps, from a count of 0 whatever the side
     took before (let y := 0; k30 y and k31 0, two steps a level of k_i x := k_(i-1) x, k0 _ := 127);
   - w_1023 (17438) and w_1024 (17464): W (1020 + 3) and W (1020 + 4) against W 1023 and W 1024, which reuse
     w_1023's lemma 127 = 127 % 256; w_mod_1023 (17540): W (1024 % 1023) against W 1; w_mod_1024 (17552):
     W (1023 % 1024) against W 1023;
   - land_65535, lor_65535, xor_65535 (19229, 19277, 19293): an operand of 65535, 30 s below; shr_15 to shr_18
     (19512 to 19537): 65535 >>> 15 = 1, and >>> 16, 17 and 18 = 0.
   No cast, and the kernel converts the two sides at once:
   - land_matchinst (16255): 255 &&& 127 at an instance whose function stops at a match; stop_ite (16637): an if;
     stop_gcd (16707): Nat.gcd 254 127, a recursion; stop_projv (16825): the projection of a pair built by an if;
     badmod_match (17916): 127 % 200 at a Mod Nat instance that stops at a match;
   - shl_17 (16530): 1 <<< 17, a shift left of more than 16, imported on its own at an Entry Timeout of 60 s:
     with no cast the kernel converts 1 <<< 17 itself, about 10 s under load (the 10 s limit of the other
     entries stopped it once); land_axiom (16590): (axN &&& 255) % 256 against
     UInt8.ofNat (axN &&& 255), axN an axiom: an operand with no value;
   - fb_65 (17010): let y := 0; k31 y, 65 steps;
   - w_1025 (17486): 1025; w_bsub (17498) and w_bxor (17510): 1025 - 1 and 1025 ^^^ 1, an operand above 1024;
     w_mod_0 (17522): 1024 % 0; w_mod_1025 (17563): 1024 % 1025, a divisor above 1024; w_match (17634): a match;
     box_param (17744): Box (Fin 256) against Box (Fin (2 ^ 8)), parameters that are no Nat terms;
   - gate_box (17785): v = boxA 0 against v = boxB 0 of type Box (Fin 256), Box a record whose field is of a
     variable's type; field_pt (17824) and field_p2 (17862): the same with a hypothesis over PT (one field, a
     proposition) or P2 (two fields); gate_glob (17894): the same, a UInt8 constant only in a global's type: the
     first scan passes none of them on, and the pass does not run;
   - land_65536, land_65537, lor_65536, xor_65536, shl_16 (19241, 19269, 19285, 19301, 19354): an operand or a
     value at or above 65536.
   No cast, and the kernel's own conversion takes longer than the limit:
   - gcd_value (16745): UInt32.ofNatLT (Nat.gcd 254 127) _ against 127, at 10 s;
   - sub_65536 (19313), div_65536 (19343), shr_big (19545): 65536 - 65409, 65536 / 512 and 5 >>> 65536, at 30 s.
   w_sub (19561): W (65535 - 64511) against W 1024, an operand above 1024: no cast.
   The budget entries (each with terms of its own, so that no run reuses a lemma of the file's cache) run, as
   tests/fin_transport_shape.v's, under Succeed at the measured largest part of the entry minus 1 (a stop), at it
   and at it plus 1 (a cast), then at the default budget (README, "Lean Transport Step Budget"; the parts are in
   the comment of the runs below):
   - bud_and (17928): and_224's shape at 224 &&& 192 against 192;
   - bud_w (17966): W (1012 + 12) against W 1024, of Fin value 126;
   - bud_fb (18158): fb_64's shape ending in 125, also stopped inside its head reduction;
   - const_only (19217): v = b128 against v = b224 &&& b128, b128 b224 : UInt8 constants, no OfNat.ofNat at a
     data record: the first scan passes it on at the constants; a ballast hypothesis makes its own part its
     largest.
   dumps/lean434/bitwise_deep.ndjson is dumps/lean434/bitwise.ndjson with deepC_lo, deepC_at and deepC_hi
   appended, Nat.land 0 (Nat.land 0 (... (Nat.land 0 0) ...)) of 9994, 9995 and 9996 applications, and the theorems
   deep_lo, deep_at and deep_hi (lines 49561, 49568, 49575): v <= UInt8.ofNatLT 0 _ against v <= UInt8.ofNat
   deepC_k, whose deepest read is at the nesting 9999, 10000 and 10001: the first two cast, the third stops.
   tests/fin_transport_bitwise.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "fin_transport_bitwise_before.log" Lean Import "../dumps/lean434/bitwise.ndjson" 1 16530.
Set Lean Entry Timeout 60.
Redirect "fin_transport_bitwise_shl17.log" Lean Import "../dumps/lean434/bitwise.ndjson" 16530 16531.
Set Lean Entry Timeout 10.
Redirect "fin_transport_bitwise.log" Lean Import "../dumps/lean434/bitwise.ndjson" 16531 17917.

Check RLI434B_and_224__nat_eq_1.
Check RLI434B_u32_and__nat_eq_1.
Check RLI434B_land_fun__nat_eq_1.
Check RLI434B_width_8__nat_eq_1.
Check RLI434B_w_1023__nat_eq_1.
Fail Check RLI434B_gcd_value.
Check RLI434B_land_axiom.
Check RLI434B_gate_box.

(* B-part: three runs of each budget entry, at its largest part (counters of this file at every part's default
   budget) - 1, at it and + 1, then the default. bud_and: its argument part
   20,770 (its own part 1,042); bud_w: its argument part 74,768 (23,914); bud_fb: its argument part 18,117
   (751); const_only: its own part 48,987 (its argument part 7,787) *)
Redirect "fin_transport_bitwise_bud_and_deps.log" Lean Import "../dumps/lean434/bitwise.ndjson" 17917 17928.
Set Lean Transport Step Budget 20769.
Redirect "fin_transport_bitwise_bud_and_stop.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17928 17929.
Set Lean Transport Step Budget 20770.
Redirect "fin_transport_bitwise_bud_and_part.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17928 17929.
Set Lean Transport Step Budget 20771.
Redirect "fin_transport_bitwise_bud_and_over.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17928 17929.
Unset Lean Transport Step Budget.
Redirect "fin_transport_bitwise_bud_and.log" Lean Import "../dumps/lean434/bitwise.ndjson" 17928 17929.

Redirect "fin_transport_bitwise_bud_w_deps.log" Lean Import "../dumps/lean434/bitwise.ndjson" 17929 17966.
Set Lean Transport Step Budget 74767.
Redirect "fin_transport_bitwise_bud_w_stop.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17966 17967.
Set Lean Transport Step Budget 74768.
Redirect "fin_transport_bitwise_bud_w_part.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17966 17967.
Set Lean Transport Step Budget 74769.
Redirect "fin_transport_bitwise_bud_w_over.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 17966 17967.
Unset Lean Transport Step Budget.
Redirect "fin_transport_bitwise_bud_w.log" Lean Import "../dumps/lean434/bitwise.ndjson" 17966 17967.

(* M2-budget: bud_fb also at N = D + F / 2: its argument part's debit D = 7,305 when the head reduction starts and
   the reduction's own debit F = 610, so that the budget runs out inside it (after a reduction that gives no
   value, fb_65's argument takes no step more). *)
Redirect "fin_transport_bitwise_bud_fb_deps.log" Lean Import "../dumps/lean434/bitwise.ndjson" 17967 18158.
Set Lean Transport Step Budget 7610.
Redirect "fin_transport_bitwise_bud_fb_whd.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 18158 18159.
Set Lean Transport Step Budget 18116.
Redirect "fin_transport_bitwise_bud_fb_stop.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 18158 18159.
Set Lean Transport Step Budget 18117.
Redirect "fin_transport_bitwise_bud_fb_part.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 18158 18159.
Set Lean Transport Step Budget 18118.
Redirect "fin_transport_bitwise_bud_fb_over.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 18158 18159.
Unset Lean Transport Step Budget.
Redirect "fin_transport_bitwise_bud_fb.log" Lean Import "../dumps/lean434/bitwise.ndjson" 18158 18159.

Redirect "fin_transport_bitwise_const_only_deps.log" Lean Import "../dumps/lean434/bitwise.ndjson" 18159 19217.
Set Lean Transport Step Budget 48986.
Redirect "fin_transport_bitwise_const_only_stop.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 19217 19218.
Set Lean Transport Step Budget 48987.
Redirect "fin_transport_bitwise_const_only_part.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 19217 19218.
Set Lean Transport Step Budget 48988.
Redirect "fin_transport_bitwise_const_only_over.log" Succeed Lean Import "../dumps/lean434/bitwise.ndjson" 19217 19218.
Unset Lean Transport Step Budget.
Redirect "fin_transport_bitwise_const_only.log" Lean Import "../dumps/lean434/bitwise.ndjson" 19217 19218.

(* K-M1: the entries with a value, operand or shift of 65535 or more, whose lemmas and conversions the kernel
   computes on operands up to 65536. *)
Set Lean Entry Timeout 30.
Redirect "fin_transport_bitwise_ceiling.log" Lean Import "../dumps/lean434/bitwise.ndjson" 19218.
Set Lean Entry Timeout 10.

(* D-depth. *)
Redirect "fin_transport_bitwise_deep.log" Lean Import "../dumps/lean434/bitwise_deep.ndjson" 19562.
Check RLI434B_deep_at__nat_eq_1.
