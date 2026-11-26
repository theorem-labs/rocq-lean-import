From LeanImport Require Import Lean.

(* The shapes the Fin case of the transport pass (README, "Transport of proof arguments across Nat literals")
   casts and the ones it leaves to the kernel. dumps/lean434/shape.ndjson is exported from
   dumps/lean434/src/RLI434Shape.lean; each theorem passes a proof of v <= a where v <= d is expected, a and d
   closed terms of the same value 127. A side may take 64 reduction steps in all: an unfolding, the
   substitution of one bound argument, a zeta step and a projection count one step each.
   Cast (a lemma on the two Fin values):
   - cast_127 (export line 8472): UInt32.ofNatLT 127 _ against (127 : UInt32);
   - result_127 (export line 8479): the result position, the theorem's own value rfl of type a = a where a = 127 is
     declared;
   - fin_and_nat (export line 8506): one argument with a Fin hole and a Nat hole (4095 + 1 against 4096), a lemma
     each;
   - chain_3 (export line 9203): three records of one field above the Fin (Int32, UInt32, BitVec 32);
   - chain_4 (export line 9247): four records (W4 over those);
   - side_63 (export line 9396): a is g27 _, a chain of functions of one argument down to UInt32.ofNatLT 127 _: 63
     steps;
   - side_64 (export line 9407): a is ge27 _, ge27 := g27 (one more unfolding): 64 steps, the most a side may take;
   - bind3_63 (export line 10055): a is t13 0 0 _, a chain of functions of three arguments, each applied to three: 63
     steps;
   - bind3_64 (export line 10068): a is te13 0 0 _, te13 := t13: 64 steps;
   - proj_63 (export line 10197): d is prj19 0, the first field of (pq19 0), pq19 a chain of definitions down to the
     pair (127, 0): 63 steps;
   - proj_64 (export line 10206): d is prje19 0, prje19 := prj19: 64 steps;
   - step_let (export line 9862): d behind a let, which head reduction passes (zeta);
   - chain_0_small (export line 10864): a bare Fin (no record above it), Fin.ofNat 256 127 against Fin.ofNat 256 383
     behind a function;
   - fin12292 (export line 10895): the definition chain_0 uses;
   - chain_0 (export line 10916): a bare Fin with a Nat of 4096 or more, Fin.ofNat 8192 4100 against Fin.ofNat 8192
     12292;
   - chain_1 (export line 10959): BitVec alone: BitVec.ofNatLT 127 _ against (127 : BitVec 32);
   - lam_63 (export line 10986): a is lam3 _: a let-bound lambda of three binders applied to three arguments, which
     zeta exposes at the head, then g24: 63 steps;
   - lam_64 (export line 11013): a is lam4 _: four binders, 64 steps;
   No cast, and the kernel's own conversion takes far longer than the 10 s limit below:
   - side_65 (9420): g28 _: 65 steps, over the 64 a side may take;
   - bind3_65 (10081): tee13 0 0 _, tee13 := te13: 65 steps;
   - proj_65 (10222): d is prj20 0: 65 steps;
   - lam_65 (11042): a is lam5 _: five binders, 65 steps;
   - chain_5 (9584): five records (W5 over W4);
   - sub_value (9616): a's value is 200 - 73, which the pass does not compute;
   - gate_const (9624): d is lit127, a constant applied to nothing, which is no Fin site (the gate looks for
     applications only), so the pass never compares the two sides;
   - stop_match (9756): d is 127 behind an if: head reduction stops at the match;
   - stop_fix (9805): d is 127 behind a structural recursion: head reduction stops at the fixpoint;
   - stop_proj (9847): d is the first field of a pair built by an if: head reduction stops at the projection of a
     match;
   No cast, and the kernel converts the two sides at once:
   - open_pair (9443): a and d are open (n and its proof are bound);
   - two_fields (9503): a pair of type Nat x Nat, a record of two fields;
   - other_width (9540): d is built at the width 31 + 1, under id: the two chains have other parameters;
   - stop_axiom (9653): both sides reduce to an axiom, where head reduction stops;
   - stop_opaque (9733): both sides reduce to the same opaque definition, which the importer declares with its value:
     head reduction unfolds it, and the two sides reach the same Fin value term;
   - mod_zero (9884): d's value is 127 % 0: a divisor of zero;
   - mod_novalue (9916): d's value is 127 % (1000 - 1): a divisor the pass does not compute;
   The src/ of the fix's parent has no Fin case and refuses cast_127 at the 10 s limit (ci/build-9.2-cut.sh
   --revert-fix). tests/fin_transport_shape.expect checks the log. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "fin_transport_shape.log" Lean Import "../dumps/lean434/shape.ndjson".

Check RLI434S_cast_127__nat_eq_1.
Check RLI434S_fin_and_nat__nat_eq_1.
Check RLI434S_chain_3__nat_eq_1.
Check RLI434S_chain_0_small__nat_eq_1.
Check RLI434S_fin12292__nat_eq_1.
Check RLI434S_chain_0__nat_eq_1.
Fail Check RLI434S_side_65.
Fail Check RLI434S_bind3_65.
Fail Check RLI434S_proj_65.
Fail Check RLI434S_lam_65.
Fail Check RLI434S_chain_5.
Fail Check RLI434S_sub_value.
Fail Check RLI434S_gate_const.
Fail Check RLI434S_stop_match.
Fail Check RLI434S_stop_fix.
Fail Check RLI434S_stop_proj.
Check RLI434S_open_pair.
Check RLI434S_two_fields.
Check RLI434S_other_width.
Check RLI434S_stop_axiom.
Check RLI434S_stop_opaque.
Check RLI434S_mod_zero.
Check RLI434S_mod_novalue.

(* Work-budget cases (dumps/lean434/fin_shape_work.ndjson, from dumps/lean434/src/RLI434ShapeWork.lean). Each
   finite setting is a measured debit of the integrated importer, read from counters of this file compiled under
   its own name (a renamed copy whose Check lines were comments measured other debits): a budget-stop case is
   set one step below the larger of the entry's own part and its largest argument part at the default budget,
   and a casting case with a finite setting at that larger part. A stop case on a UInt32 pair leaves Lean's
   value to the kernel, whose conversion of UInt32 values outlasts the 20 s limit. *)
Set Lean Entry Timeout 20.

(* W03b: a small monomorphic Fin case still casts. *)
Redirect "fin_transport_shape_ordinary_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 1 8485.
Redirect "fin_transport_shape_ordinary.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8485 8486.
Check RLI434SW_ordinary.

(* W03b: charge a polymorphic body before instantiating it on the Fin head path. *)
Redirect "fin_transport_shape_poly_body_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8486 8862.
Set Lean Transport Step Budget 4084.
Redirect "fin_transport_shape_poly_body_precharge.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8862 8863.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_poly_body.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8862 8863.
Check RLI434SW_poly_body.

(* W09a: cast the side closed by the inner lambda. Decline the open side
   under the forall, whose application on its own does not bind x. *)
Redirect "fin_transport_shape_binder_depth_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8863 8969.
Set Lean Transport Step Budget 2492.
Redirect "fin_transport_shape_binder_depth_closed.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8969 8970.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_binder_depth.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8969 8970.
Check RLI434SW_binder_depth.

(* W09b: non-identical parameter trees compare equal; their walk is charged. *)
Redirect "fin_transport_shape_parameters_equal_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 8970 9036.
Set Lean Transport Step Budget 10329.
Redirect "fin_transport_shape_parameters_equal_parameters.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9036 9037.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_parameters_equal.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9036 9037.
Check RLI434SW_parameters_equal.

(* W09b: different parameter expressions do not cast, even if convertible. *)
Redirect "fin_transport_shape_parameters_differ_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9037 9084.
Redirect "fin_transport_shape_parameters_differ.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9084 9085.
Check RLI434SW_parameters_differ.

(* W10a: beta duplication must pay before copying. *)
Redirect "fin_transport_shape_beta_subst_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9085 9428.
Set Lean Transport Step Budget 56139.
Redirect "fin_transport_shape_beta_subst_beta.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9428 9429.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_beta_subst.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9428 9429.
Check RLI434SW_beta_subst.

(* W10a: let duplication must pay before copying. *)
Redirect "fin_transport_shape_let_subst_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9429 9441.
Set Lean Transport Step Budget 56135.
Redirect "fin_transport_shape_let_subst_zeta.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9441 9442.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_let_subst.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9441 9442.
Check RLI434SW_let_subst.

(* W10b: set N between early and late argument-part costs. Only the unrelated Fin hole casts. N is the largest
   part of the entry (the other Fin hole's argument), below the wide pair's argument part under the measured
   mutant that checks the 64-step limit only after all of wideA's binders are substituted. *)
Redirect "fin_transport_shape_early_cap_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9442 9824.
Set Lean Transport Step Budget 6313.
Redirect "fin_transport_shape_early_cap.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9824 9825.
Check RLI434SW_early_cap.
Unset Lean Transport Step Budget.

(* W10d: charge each wide application copy, including when flattening the new head. *)
Redirect "fin_transport_shape_flatten_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9825 9955.
Set Lean Transport Step Budget 2719.
Redirect "fin_transport_shape_flatten_slice.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9955 9956.
Unset Lean Transport Step Budget.
Set Lean Transport Step Budget 2719.
Redirect "fin_transport_shape_flatten_flatten.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9955 9956.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_flatten.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9955 9956.
Check RLI434SW_flatten.

(* W14b: the expected type of the result applies the long Fin head, and the transport casts. Its peel runs in
   the result walk's gate, in the entry's own part, so W14b's stop case is on product_peel_arg below. *)
Redirect "fin_transport_shape_product_peel_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 9956 10081.
Redirect "fin_transport_shape_product_peel.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10081 10082.
Check RLI434SW_product_peel.

(* W26a: small sharing created by head reduction still allows transport. *)
Redirect "fin_transport_shape_head_fits_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10082 10137.
Redirect "fin_transport_shape_head_fits.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10137 10138.
Check RLI434SW_head_fits.

(* W26a: head reduction creates a large shared replacement; stop and preserve Lean’s original declaration. *)
Redirect "fin_transport_shape_head_overflow_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10138 10299.
Set Lean Transport Step Budget 4611686018427387903.
Redirect "fin_transport_shape_head_overflow.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10299 10300.
Check RLI434SW_head_overflow.
Unset Lean Transport Step Budget.

(* W14b: the long Fin head in the expected type of an argument: that argument's gate is the first to read the
   head, and peels its product chain in the argument's own part, the entry's largest part (3,165 steps; the own
   part 558; counters of this file, run r8mut-cnt2-20261126t094103). The stop case is one step below that part;
   Lean's value then goes to the kernel, whose conversion of the UInt32 values outlasts the 20 s limit. *)
Redirect "fin_transport_shape_product_peel_arg_deps.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10300 10327.
Set Lean Transport Step Budget 3164.
Redirect "fin_transport_shape_product_peel_arg_peel.log" Succeed Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10327 10328.
Unset Lean Transport Step Budget.
Redirect "fin_transport_shape_product_peel_arg.log" Lean Import "../dumps/lean434/fin_shape_work.ndjson" 10327 10328.
Check RLI434SW_product_peel_arg.
