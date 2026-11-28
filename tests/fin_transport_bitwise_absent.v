From LeanImport Require Import Lean.

(* The bitwise Fin case of the transport pass (README, "Transport of proof arguments across Nat literals") when
   the export lacks a name it looks for, and a Fin pair whose parameters differ.
   dumps/lean434/bitwise_noofnat.ndjson (lean4export RLI434Bitwise -- RLI434B.noofnat) holds no OfNat.ofNat: it is
   imported first, in a document that has imported nothing, since the export's constants of a name are the ones
   the document has declared so far. noofnat : forall b : Bool, (!b) = false -> (!b) = false (export line 122)
   names Bool.not, an application headed by a constant, which the first scan compares with the empty list of
   OfNat.ofNat: the entry imports with no line about it.
   dumps/lean434/bitwise_absent.ndjson is dumps/lean434/bitwise.ndjson with Nat.land, HOr.hOr and Nat.instXorOp
   renamed Nat.landLib, HOr.hOrLib and Nat.instXorOpLib, and RLI434B.w_differ appended (its row in
   dumps/lean434/README.md); its lines before line 15249 are Init's. This file imports the lines of each entry
   below and the declarations they need (GT.gt, line 16556), and none of the other RLI434B entries:
   - u32_lor (line 15810): UInt32.ofNatLT 255 _ against UInt32.ofNat (255 ||| 0), where the row of ||| has no
     class function: the head reduction takes 255 ||| 0 to Nat.lor 255 0, which its function arm reads, and the
     argument is cast. The src/ of the fix's parent has no bitwise Fin case and refuses u32_lor at the 10 s limit
     below (ci/build-9.2-cut.sh --revert-fix): Rocq's kernel converts a UInt32 value through 2 ^ 32 on the unary
     Nat;
   - land_fun (line 15875): UInt8.ofNatLT 127 _ against UInt8.ofNat (Nat.landLib 255 127): the row of &&& has no
     function, Nat.landLib 255 127 is no row's form, and the head reduction stops at its recursion: no cast, and
     the kernel converts the two sides;
   - land_class (line 15881): 255 &&& 127, the class function at Nat's instance: read, and cast;
   - lor_class (line 15904): 255 ||| 127 against 255, cast through the head reduction to Nat.lor 255 127;
   - xor_both (line 16158): 255 ^^^ 15 against 240, where the instance pattern of ^^^ names an absent constant:
     no row's form, and the head reduction takes it to Nat.xor 255 15, which is read: cast;
   - W, W.ofA, lt127 and W.ofB (lines 17035, 17048, 17061, 17408), and w_differ (line 19573):
     forall v : W 1024, v = W.ofA (1020 + 4) 127 _ -> v = W.ofB 1024 127, of value fun v (h : v = W.ofA 1023 127 _)
     => h, whose parameters 1023 and 1024 differ: no cast, and the kernel refuses Lean's value, whose binder type
     is ill-typed.
   No entry makes the pass fail. tests/fin_transport_bitwise_absent.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "fin_transport_bitwise_noofnat.log" Lean Import "../dumps/lean434/bitwise_noofnat.ndjson".
Redirect "fin_transport_bitwise_absent_init.log" Lean Import "../dumps/lean434/bitwise_absent.ndjson" 1 15249.
Redirect "fin_transport_bitwise_absent_deps.log" Lean Import "../dumps/lean434/bitwise_absent.ndjson" 15280 15648.
Redirect "fin_transport_bitwise_absent.log" Lean Import "../dumps/lean434/bitwise_absent.ndjson" 15649 16159.
Redirect "fin_transport_bitwise_absent_gt.log" Lean Import "../dumps/lean434/bitwise_absent.ndjson" 16556 16557.
Redirect "fin_transport_bitwise_absent_w.log" Lean Import "../dumps/lean434/bitwise_absent.ndjson" 17011 17438.
Redirect "fin_transport_bitwise_absent_differ.log" Lean Import "../dumps/lean434/bitwise_absent.ndjson" 19562.

Check RLI434B_noofnat.
Check RLI434B_u32_lor__nat_eq_1.
Check RLI434B_land_class__nat_eq_1.
Check RLI434B_lor_class__nat_eq_1.
Check RLI434B_xor_both__nat_eq_1.
Check RLI434B_land_fun.
Fail Check RLI434B_w_differ.
