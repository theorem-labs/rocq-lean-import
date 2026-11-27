From LeanImport Require Import Lean.

(* Literal arithmetic, the held operations and their values (README, "Transport of proof arguments across Nat
   literals"): a Nat operation is held when an operand or its value is 65536 or more, or an operand is held, and
   gets its value by a sub-lemma: the Add, Mul and Pow rows' certificates, toN_sub for a subtraction, and Lean's
   Nat.div_eq_of_lt_le for a division. dumps/lean434/litarith.ndjson: the definitions (lines 1 to 23878), then
   this test's theorems (lines 24191 to 24558). Cast:
   - div_held_l (24206): 4294967296 / 64 against 67108864, the roots' division; the test's own entry, which the
     src/ of the fix's parent leaves to the kernel, refused at the 10 s limit;
   - hmin_* (24213 to 24299): each held function at the threshold: an operand at 65535, 65536, 65537 with a small
     value (65535 - 65534, ..., 65537 / 2, 65536 * 1) and a value at 65535, 65536, 65537 from small operands
     (32768 + 32767, ..., 256 * 256, 2 ^ 16): below 65536 computed with no sub-lemma, from 65536 held;
   - h_operand (24307): (4294967296 - (4294967296 - 5)) - 2, a small operation over a held operand;
   - lit_4999, lit_5000, lit_5001 (24326, 24337, 24352): 65536 - 60537 to 65536 - 60535, where the importer's
     literal changes form (unary below 5000, binary from it);
   - mod_65535 (24360): 65535 % 7, computed; mod_in_form_cls (24388): 65536 % 7 by the class function in a
     constructor's parameter, which no reader reads; beq_small_t, beq_small_f, ble_small (24395, 24406, 24412):
     Nat.beq and Nat.ble on two literals below 65536, computed to their Bool constructor;
   - sub_held (24441), sub_held_l (24452): 65536 - 31 and 4294967296 - 16 at Nat; sub_trunc (24460): a held
     subtraction Lean truncates at 0; div_held (24467): 65536 / 64;
   - two_pairs_subfail (24480): 65536 / 0 beside a second place: no certificate for a division by 0, that pair no
     lemma, the second place cast; z_ord (24491): 5000 + 65536 / 0 against 5000 beside 2 ^ 32 against 4294967296:
     the ordinary reader reads no division, the evaluator's pair gets no sub-lemma, the second place is cast;
   - bits_1023, bits_1024 (24526, 24538): products of 1023 and 1024 bits beside the replacement field, revision
     8's Nat case; lbits_1023, lbits_1024 (24544, 24550): the same products held by the evaluation; pow_1024b
     (24558): 2 ^ 1023 on both sides, held. These five are imported on their own at an Entry Timeout of 60 s
     (the kernel's check of bits_1024 took 13.1 s on the narrowed prototype);
   - div_held_d (26050, after the lines of every other test): Nat.div 4294967296 64 against 67108864, the held
     division in the direct form Nat.div: its sub-lemma is Lean's Nat.div_eq_of_lt_le, stated by HDiv.hDiv, cast
     along the bridge the kernel checks on two variables (at the literals it would compute Nat.div on the unary
     Nat);
   - held_rep_ops (26099): mk2 (2 ^ 32) 4294967296 against (2 ^ 32 + 1, 4294967296 + 1), mk2 x y := (x + 1, y + 1):
     two held additions of one function, form and pair of values whose first operands are different terms, each
     its own representative, so that the kernel never converts the literal 4294967296 with 2 ^ 32 (which it would
     compute on the unary Nat past the 10 s limit);
   - held_small_param (26145): a pair at Fin (Nat.pow 2 8) × Nat whose held 65536 - 31 stands at an evaluated
     position and whose direct Nat.pow 2 8, below 65536, in the Fin's bound and its proof's type is not held (a
     motive abstracting it there is ill-typed), beside the Nat place 2 ^ 32 against 4294967296 of the same
     argument: both places cast.
   No line, the entry declared:
   - unvalued_head (24315): axF 3 + 3, an operand no reader reads; mod_65536 (24368): a held %; mod_in_form
     (24378): Lean's Nat.mod 65536 7 in a constructor's parameter, a held %; beq_big, beq_big1, ble_big, beq_held
     (24418 to 24436): Nat.beq and Nat.ble on an operand of 65536 or more, or held; pow_1025b (24514): 2 ^ 1024 on
     both sides, 1025 bits, which no reader values: the kernel converts the two constants without computing it.
   No line, the kernel refuses the entry at the 10 s limit:
   - bits_1025 (24506): a product of 1025 bits, which no reader values.
   tests/litarith_hold.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "litarith_hold_lib.log" Lean Import "../dumps/lean434/litarith.ndjson" 1 23879.
Redirect "litarith_hold.log" Lean Import "../dumps/lean434/litarith.ndjson" 24191 24515.
Set Lean Entry Timeout 60.
Redirect "litarith_hold_bits.log" Lean Import "../dumps/lean434/litarith.ndjson" 24515 24559.
Set Lean Entry Timeout 10.
Redirect "litarith_hold_d.log" Lean Import "../dumps/lean434/litarith.ndjson" 26044 26051.
Redirect "litarith_hold_rep.log" Lean Import "../dumps/lean434/litarith.ndjson" 26077 26146.

(* Every lemma a cast above uses exists; a lemma the kernel refused was not declared. *)
Check RLI434L_div_held_l__nat_eq_2.
Check RLI434L_hmin_sub_op_65535__nat_eq_2.
Check RLI434L_hmin_sub_op_65536__nat_eq_2.
Check RLI434L_hmin_sub_op_65537__nat_eq_2.
Check RLI434L_hmin_div_op_65535__nat_eq_1.
Check RLI434L_hmin_div_op_65536__nat_eq_2.
Check RLI434L_hmin_div_op_65537__nat_eq_2.
Check RLI434L_hmin_mul_op_65536__nat_eq_2.
Check RLI434L_hmin_add_val_65535__nat_eq_1.
Check RLI434L_hmin_add_val_65536__nat_eq_2.
Check RLI434L_hmin_add_val_65537__nat_eq_2.
Check RLI434L_hmin_mul_val_65535__nat_eq_1.
Check RLI434L_hmin_mul_val_65536__nat_eq_2.
Check RLI434L_hmin_pow_val_65536__nat_eq_2.
Check RLI434L_h_operand__nat_eq_2.
Check RLI434L_lit_4999__nat_eq_2.
Check RLI434L_lit_5000__nat_eq_2.
Check RLI434L_lit_5001__nat_eq_2.
Check RLI434L_mod_65535__nat_eq_1.
Check RLI434L_mod_in_form_cls__nat_eq_1.
Check RLI434L_beq_small_t__nat_eq_1.
Check RLI434L_beq_small_f__nat_eq_2.
Check RLI434L_ble_small__nat_eq_1.
Check RLI434L_sub_held__nat_eq_1.
Check RLI434L_sub_held_l__nat_eq_2.
Check RLI434L_sub_trunc__nat_eq_2.
Check RLI434L_div_held__nat_eq_2.
Check RLI434L_two_pairs_subfail__nat_eq_1.
Check RLI434L_z_ord__nat_eq_1.
Check RLI434L_bits_1023__nat_eq_1.
Check RLI434L_bits_1024__nat_eq_1.
Check RLI434L_lbits_1023__nat_eq_2.
Check RLI434L_lbits_1024__nat_eq_2.
Check RLI434L_pow_1024b__nat_eq_2.
Check RLI434L_mpf_a__proof_1__nat_eq_1.
Check RLI434L_mpf_a__proof_2__nat_eq_1.
