From LeanImport Require Import Lean.

(* Regression for #63: Lean's Inhabited instantiated at Prop (mapped to
   SProp) must still support projection and dependent elimination. *)

Redirect "inhabited_sprop.log" Lean Import "../dumps/inhabited_sprop" 1 107.

Check test.

(* At α : Prop, [Inhabited'_inst1] is a record in Type whose only field is in
   SProp. Rocq gives definitional eta to such a record only with universe
   checking off (type in type), which the import never turns off, so it is
   declared as a non-primitive record, without eta: the eta equation is a
   well-typed statement that [eq_refl] does not prove. *)
Definition get_default_inst1 {A : SProp} (x : Inhabited'_inst1 A) : A :=
  match x with Inhabited'_mk_inst1 _ v => v end.

Check fun (A : SProp) (x : Inhabited'_inst1 A) =>
  Inhabited'_mk_inst1 A (get_default_inst1 x) = x.
Fail Check fun (A : SProp) (x : Inhabited'_inst1 A) =>
  (eq_refl : Inhabited'_mk_inst1 A (get_default_inst1 x) = x).

(* Line 107 declares [test_eta := Inhabited'.eta MyProp h2], which needs
   [Inhabited'.eta] at α : Prop. Lean proves [Inhabited'.eta] by [rfl], that is
   by eta for [Inhabited'_inst1], so this Rocq rejects it, and [test_eta] is not
   declared. *)
Redirect "inhabited_sprop_eta.log" Fail Lean Import "../dumps/inhabited_sprop" 107.
Fail Check test_eta.

Definition get_default {A} (x : Inhabited' A) : A :=
  match x with Inhabited'_mk _ v => v end.

Lemma inhabited_eta {A} (x : Inhabited' A) :
  Inhabited'_mk A (get_default x) = x.
Proof. destruct x; reflexivity. Qed.
