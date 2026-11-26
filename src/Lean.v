From Stdlib Require ZArith NArith Lia ZifyBool Uint63.
Declare ML Module "coq-lean-import.plugin".

Set Universe Polymorphism.
Set Printing Universes.
Set Primitive Projections.

Declare Scope lean_scope.
Global Open Scope lean_scope.

Global Set Definitional UIP.

Cumulative
Inductive eq@{u|} {α:Type@{u}} (a:α) : α -> SProp
  := eq_refl : eq a a.
Notation "x = y" := (eq x y) : lean_scope.

Register eq as lean.Eq.

Inductive eq_inst1@{|} {α:SProp} (a:α) : α -> SProp
  := eq_refl_inst1 : eq_inst1 a a.

Register eq_inst1 as lean.Eq_inst1.

(* Inductive List@{u Lean.u+1.0} (α : Type@{Lean.u+1.0}) : Type@{Lean.u+1.0} :=
    List_nil : List@{u Lean.u+1.0} α
  | List_cons : α -> List@{u Lean.u+1.0} α -> List@{u Lean.u+1.0} α. *)

Monomorphic Universe set.
Inductive List_inst1@{} (α : Type@{set}) : Type@{set} :=
| List_nil_inst1 : List_inst1 α
| List_cons_inst1 : α -> List_inst1 α -> List_inst1 α.

Register List_inst1 as lean.List_inst1.

Module Quot.

  Private Inductive quot@{u|} {α : Type@{u}} (r : α -> α -> SProp) : Type@{u}
    := mk (a:α).

  Register quot as lean.Quot.
  Register mk as lean.Quot.mk.

  Definition lift@{u v|} {α : Type@{u}} {r:α -> α -> SProp} {β : Type@{v}} (f : α -> β)
    : (forall a b : α, r a b -> eq (f a) (f b)) -> quot r -> β
    := fun H q => match q with mk _ x => fun _ => f x end H.

  Register lift as lean.Quot.lift.

  Definition lift_inst2@{u|} {α : Type@{u}} {r:α -> α -> SProp} {β : SProp} (f : α -> β)
    : (forall a b : α, r a b -> eq_inst1 (f a) (f b)) -> quot r -> β
    := fun H q => match q with mk _ x => fun _ => f x end H.

  Register lift_inst2 as lean.Quot.lift_inst2.

  Definition ind@{u|} {α : Type@{u}} {r:α -> α -> SProp} {β : quot r -> SProp}
    : (forall a : α, β (mk r a)) -> forall q : quot r, β q
    := fun f q => match q with mk _ x => f x end.

  Register ind as lean.Quot.ind.

  (* Because quot_inst1 is SProp we don't need to make it Private: the
     axiom declared by lean about it is a tautology. *)
  Inductive quot_inst1@{|} {α : SProp} (r : α -> α -> SProp) : SProp
    := mk_inst1 (a:α).

  Register quot_inst1 as lean.Quot_inst1.
  Register mk_inst1 as lean.Quot.mk_inst1.

  (* This non-uniform translation avoids breaking SR ;) *)
  Definition lift_inst1@{v|} {α : SProp} {r:α -> α -> SProp} {β : Type@{v}} (f : α -> β)
    : (forall a b : α, r a b -> eq (f a) (f b)) -> quot_inst1 r -> β
    := fun _ q => f (match q with mk_inst1 _ x => x end).

  Register lift_inst1 as lean.Quot.lift_inst1.

  Definition lift_inst3@{|} {α : SProp} {r:α -> α -> SProp} {β : SProp} (f : α -> β)
    : (forall a b : α, r a b -> eq_inst1 (f a) (f b)) -> quot_inst1 r -> β
    := fun _ q => f (match q with mk_inst1 _ x => x end).

  Register lift_inst3 as lean.Quot.lift_inst3.

  Definition ind_inst1@{|} {α : SProp} {r:α -> α -> SProp} {β : quot_inst1 r -> SProp}
    : (forall a : α, β (mk_inst1 r a)) -> forall q : quot_inst1 r, β q
    := fun f q => match q with mk_inst1 _ x => f x end.

  Register ind_inst1 as lean.Quot.ind_inst1.

End Quot.

Inductive Nat := Nat_zero : Nat | Nat_succ : Nat -> Nat.

Register Nat as lean.Nat.

Fixpoint double (n : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => Nat_succ (Nat_succ (double n))
  end.

Register double as lean.Nat_double.

Declare Scope Nat_scope.
Delimit Scope Nat_scope with Nat.
Open Scope Nat_scope.
Bind Scope Nat_scope with Nat.

Inductive Nat_le@{} (n : Nat) : Nat -> SProp :=
| Nat_le_refl : Nat_le n n
| Nat_le_step : forall m : Nat, Nat_le n m -> Nat_le n (Nat_succ m).

Register Nat_le as lean.Nat_le.

Notation "n <= m" := (Nat_le n m) : Nat_scope.
Notation "n < m" := (Nat_le (Nat_succ n) m) (only parsing) : Nat_scope.
(*
Definition Nat_pred (n : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => n
  end. *)

Variant Or@{} (a a0 : SProp) : SProp :=
| Or_inl : a -> Or a a0
| Or_inr : a0 -> Or a a0.
Register Or as lean.Or.
Record And@{} (a a0 : SProp) : SProp := And_intro
  { left : a;  right : a0 }.
Register And as lean.And.

Inductive sEmpty : SProp := .

Section nat_notation.
  Import ZifyClasses ZArith NArith.
  Fixpoint nat_of_Nat (n : Nat) : nat :=
    match n with
    | Nat_zero => 0
    | Nat_succ n => S (nat_of_Nat n)
    end%nat.
  Fixpoint Nat_of_nat (n : nat) : Nat :=
    match n with
    | O => Nat_zero
    | S n => Nat_succ (Nat_of_nat n)
    end.

  Definition Nat_of_N (n : N) : Nat := Nat_of_nat (N.to_nat n).
  Definition N_of_Nat (n : Nat) : N := N.of_nat (nat_of_Nat n).
  Definition Nat_of_num_uint n : Nat := Nat_of_N (N.of_num_uint n).
  Definition Nat_to_num_uint (n : Nat) := N.to_num_uint (N_of_Nat n).

  Lemma nat2Natid (n : nat) : nat_of_Nat (Nat_of_nat n) = n.
  Proof. induction n as [|n IHn]; cbn; rewrite ?IHn; reflexivity. Qed.
  Lemma Nat2natid (n : Nat) : Nat_of_nat (nat_of_Nat n) = n.
  Proof. induction n as [|n IHn]; cbn; rewrite ?IHn; reflexivity. Qed.

  #[global]
  Monomorphic Instance Inj_Nat_Z : InjTyp Nat Z :=
    mkinj _ _ (fun n => Z.of_nat (nat_of_Nat n)) (fun x =>  0 <= x )%Z (fun n => Nat2Z.is_nonneg _).

  Lemma nat_le_Nat_le' (n m : nat) : (n <= m)%nat -> (Nat_of_nat n <= Nat_of_nat m)%Nat.
  Proof. induction 1; cbn; constructor; assumption. Defined.

  Lemma nat_le_Nat_le (n m : Nat) : (nat_of_Nat n <= nat_of_Nat m)%nat -> (n <= m)%Nat.
  Proof.
    intro H; apply nat_le_Nat_le' in H.
    rewrite !Nat2natid in H; assumption.
  Qed.

  Definition Nat_le_ind (n : Nat) (P : forall m, n <= m -> Prop)
              (H0 : P n (Nat_le_refl n))
              (HS : forall m (H : n <= m), P m H -> P (Nat_succ m) (Nat_le_step n m H))
              m (H : n <= m) : P m H.
  Proof.
    revert m H; fix IH 1; intros [|m] H; [ clear IH | specialize (IH m) ].
    { clear HS.
      revert n P H0 H.
      fix IH 1; intros [|n] P H0 H; [ clear IH | specialize (IH n) ].
      { exact H0. }
      { cut sEmpty; [ destruct 1 | ].
        inversion H. } }
    { specialize (fun H => HS m _ (IH H)).
      clear IH.
      destruct (Nat.eqb (nat_of_Nat n) (nat_of_Nat (Nat_succ m))) eqn:E; [ clear HS | clear H0 ].
      { apply Nat.eqb_eq in E.
        apply (f_equal Nat_of_nat) in E.
        rewrite !Nat2natid in E.
        subst.
        exact H0. }
      { refine (HS _); clear HS.
        inversion H; subst; rewrite ?Nat.eqb_refl in E.
        { congruence. }
        { assumption. } } }
  Qed.

  Register Scheme Nat_le_ind as ind_dep for Nat_le.

  Definition Nat_le_rect (n : Nat) (P : forall m, n <= m -> Type)
              (H0 : P n (Nat_le_refl n))
              (HS : forall m (H : n <= m), P m H -> P (Nat_succ m) (Nat_le_step n m H))
              m (H : n <= m) : P m H.
  Proof.
    revert m H; fix IH 1; intros [|m] H; [ clear IH | specialize (IH m) ].
    { clear HS.
      revert n P H0 H.
      fix IH 1; intros [|n] P H0 H; [ clear IH | specialize (IH n) ].
      { exact H0. }
      { cut sEmpty; [ destruct 1 | ].
        inversion H. } }
    { specialize (fun H => HS m _ (IH H)).
      clear IH.
      destruct (Nat.eqb (nat_of_Nat n) (nat_of_Nat (Nat_succ m))) eqn:E; [ clear HS | clear H0 ].
      { apply Nat.eqb_eq in E.
        apply (f_equal Nat_of_nat) in E.
        rewrite !Nat2natid in E.
        subst.
        exact H0. }
      { refine (HS _); clear HS.
        inversion H; subst; rewrite ?Nat.eqb_refl in E.
        { congruence. }
        { assumption. } } }
  Defined.

  Register Scheme Nat_le_rect as rect_dep for Nat_le.

  Lemma Nat_le_nat_le' (n m : Nat) : (n <= m)%Nat -> (nat_of_Nat n <= nat_of_Nat m)%nat.
  Proof. induction 1; cbn; constructor; assumption. Defined.

  Lemma Nat_le_nat_le (n m : nat) : (Nat_of_nat n <= Nat_of_nat m)%Nat -> (n <= m)%nat.
  Proof.
    intro H; apply Nat_le_nat_le' in H.
    rewrite !nat2Natid in H; assumption.
  Qed.
End nat_notation.
Add Zify InjTyp Inj_Nat_Z.

Number Notation Nat Nat_of_num_uint Nat_to_num_uint (abstract after 5000) : Nat_scope.
(* Tell the kernel to unfold these wrappers early, to speed things up *)
#[global] Strategy -10000 [Nat_of_num_uint Nat_to_num_uint].

#[local] Set Warnings "-abstract-large-number".
Definition UInt32_size : Nat := 0x100000000%Nat.
Register UInt32_size as lean.UInt32_size.

Record Fin@{} (n : Nat) := Fin_mk { val : Nat; isLt : (val < n)%Nat }.
Register Fin as lean.Fin.

(* [UInt32] shape changed in Lean 4.17 from [Fin UInt32_size] to
   [BitVec 32]; [lean.UInt32] is the new default, [lean.UInt32.legacy]
   the old.  Dispatcher in lean.ml picks based on the [#IND] ctor. *)

Fixpoint Nat_add (n m : Nat) : Nat :=
  match n with
  | Nat_zero => m
  | Nat_succ n => Nat_succ (Nat_add n m)
  end.

Fixpoint Nat_mul (n m : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => Nat_add m (Nat_mul n m)
  end.

Fixpoint Nat_pow (b e : Nat) : Nat :=
  match e with
  | Nat_zero => Nat_succ Nat_zero
  | Nat_succ e => Nat_mul b (Nat_pow b e)
  end.
Register Nat_pow as lean.Nat_pow.

Record BitVec@{} (w : Nat) : Type := BitVec_mk { toFin : Fin (Nat_pow 2 w) }.
Register BitVec as lean.BitVec.

Record UInt32_legacy@{} := UInt32_legacy_mk { val0 : Fin UInt32_size }.
Register UInt32_legacy as lean.UInt32.legacy.

Record UInt32@{} := UInt32_mk { toBitVec : BitVec 32 }.
Register UInt32 as lean.UInt32.


Section strings.
  Import ZArith NArith Lia Zify ZifyBool.
  Variant InvalidUInt32 (n : N) : Set := invalid_uint32.
  Variant InvalidChar (n : N) : Set := invalid_char.
  #[local] Set Warnings "-abstract-large-number".

  Lemma Nat_lt_to_N (n : N) (m : N) : (n <? m)%N = true -> Nat_of_N n < Nat_of_N m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite ?nat2Natid.
    lia.
  Qed.

  Lemma Nat_lt_to_N_l (n : Nat) (m : N) : (N_of_Nat n <? m)%N = true -> n < Nat_of_N m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite nat2Natid.
    lia.
  Qed.

  Lemma Nat_lt_to_N_r (n : N) (m : Nat) : (n <? N_of_Nat m)%N = true -> Nat_of_N n < m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite nat2Natid.
    lia.
  Qed.

  (* Section with_or. *)
    (* Context (Or : SProp -> SProp -> SProp)
            (Or_inl : forall P Q, P -> Or P Q)
            (Or_inr : forall P Q, Q -> Or P Q)
            (And : SProp -> SProp -> SProp)
            (And_intro : forall P Q, P -> Q -> And P Q). *)
  #[local] Set Warnings "-notation-overridden".
  #[local] Infix "\/" := Or : type_scope.
  #[local] Infix "/\" := And : type_scope.
  #[local] Open Scope Nat_scope.

  Definition Nat_isValidChar (n : Nat) : SProp
    := n < 0xd800 \/ (0xdfff < n /\ n < 0x110000).

  Record Char_legacy@{} := Char_legacy_mk
  { val1_legacy : UInt32_legacy; valid_legacy : Nat_isValidChar val1_legacy.(val0).(val _) }.

  Record Char@{} := Char_mk
  { val1 : UInt32; valid : Nat_isValidChar val1.(toBitVec).(toFin _).(val _) }.

  Definition check_N_isValidChar (n : N) : bool
    := ((n <? 0xd800) || ((0xdfff <? n) && (n <? 0x110000)))%N%bool.

  Definition Fin_mk_N (n : N) (val : N) (isLt : (val <? n)%N = true) : Fin (Nat_of_N n)
    := Fin_mk (Nat_of_N n) (Nat_of_N val) (Nat_lt_to_N val n isLt).

  Definition UInt32_legacy_mk_N (val : N) (isLt : (val <? 0x100000000)%N = true) : UInt32_legacy
    := UInt32_legacy_mk (Fin_mk_N 0x100000000 val isLt).

  Lemma Nat_isValidChar_mk_N (n : N) (isLt : check_N_isValidChar n = true)
    : Nat_isValidChar (Nat_of_N n).
  Proof.
    cbv [Nat_isValidChar Nat_of_num_uint check_N_isValidChar] in *.
    pose proof (Nat_lt_to_N n 0xd800) as H1.
    pose proof (Nat_lt_to_N 0xdfff n) as H2.
    pose proof (Nat_lt_to_N n 0x110000) as H3.
    destruct N.ltb; cbn [orb] in *;
    [ | destruct N.ltb; cbn [andb] in *; [ | exfalso; congruence ] ];
    [ | destruct N.ltb; cbn [andb] in *; [ | exfalso; congruence ] ];
    [ apply Or_inl, nat_le_Nat_le; revert H1 | apply Or_inr, And_intro; apply nat_le_Nat_le; [ revert H2 | revert H3 ] ];
    clear.
    all: cbv [Nat_of_N Nat_of_num_uint].
    all: intro H; specialize (H Logic.eq_refl).
    all: apply Nat_le_nat_le' in H.
    1: etransitivity; [ exact H | ].
    2: etransitivity; [ | exact H ].
    3: etransitivity; [ exact H | ].
    all: clear.
    all: zify; clear.
    all: cbn [nat_of_Nat]; rewrite ?nat2Natid, ?Nat2Z.inj_succ, ?N_nat_Z.
    all: vm_compute; congruence.
  Qed.

  Definition Char_legacy_mk_N (val : N) (isLt : ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = true) : Char_legacy
    := Char_legacy_mk (UInt32_legacy_mk_N val (proj1 (andb_prop _ _ isLt))) (Nat_isValidChar_mk_N val (proj2 (andb_prop _ _ isLt))).

  Definition reflective_Char_legacy_mk (val : N)
    : if ((val <? 0x100000000)%N && check_N_isValidChar val)%bool
      then Char_legacy
      else InvalidChar val
    := let isLt := ((val <? 0x100000000)%N && check_N_isValidChar val)%bool in
       match isLt return ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = isLt -> if isLt then Char_legacy else InvalidChar val with
       | true => fun H => Char_legacy_mk_N val H
       | false => fun _ => invalid_char val
       end Logic.eq_refl.

  Definition reflective_Char_legacy_mk_prim (val : Uint63.int)
    := reflective_Char_legacy_mk (Z.to_N (Uint63.to_Z val)).


  (* Definition reflective_UInt32_mk (val : N) : if (val <? 0x100000000)%N
                                              then UInt32
                                              else InvalidUInt32 val
    := let isLt := (val <? 0x100000000)%N in
       match isLt return (val <? 0x100000000)%N = isLt -> if isLt then UInt32 else InvalidUInt32 val with
       | true => fun H => UInt32_mk_N val H
       | false => fun _ => invalid_uint32 val
       end Logic.eq_refl.

  Definition reflective_UInt32_mk_prim (val : Uint63.int)
    := reflective_UInt32_mk (Z.to_N (Uint63.to_Z val)).


  Definition check_isValidChar (n : Nat) : bool
    := let n := N_of_Nat n in
        ((n <? 0xd800) || ((0xdfff <? n) && (n <? 0x110000)))%N%bool.

  Definition reflective_isValidChar_mk (n : Nat)
    : if check_isValidChar n
      then n < 0xd800 \/ (0xdfff < n /\ n < 0x110000)
      else InvalidChar n.
  Proof.
    cbv [check_isValidChar].
    pose proof (Nat_lt_to_N_l n 0xd800) as H1.
    pose proof (Nat_lt_to_N_r 0xdfff n) as H2.
    pose proof (Nat_lt_to_N_l n 0x110000) as H3.
    destruct N.ltb; cbn [orb];
    [ | destruct N.ltb; cbn [andb]; [ | constructor ] ];
    [ | destruct N.ltb; cbn [andb]; [ | constructor ] ];
    [ apply Or_inl, nat_le_Nat_le; revert H1 | apply Or_inr, And_intro; apply nat_le_Nat_le; [ revert H2 | revert H3 ] ];
    clear.
    all: cbv [Nat_of_N Nat_of_num_uint].
    all: intro H; specialize (H Logic.eq_refl).
    all: apply Nat_le_nat_le' in H.
    1: etransitivity; [ exact H | ].
    2: etransitivity; [ | exact H ].
    3: etransitivity; [ exact H | ].
    all: clear.
    all: zify; clear.
    all: cbn [nat_of_Nat]; rewrite ?nat2Natid, ?Nat2Z.inj_succ, ?N_nat_Z.
    all: vm_compute; congruence.
  Qed.
  End with_or. *)


End strings.

Register Nat_isValidChar as lean.Nat_isValidChar.
Register Char as lean.Char.
Register Char_legacy as lean.Char.legacy.
Register reflective_Char_legacy_mk_prim as lean.Char.legacy.mk.reflective_prim.
(* On the new path (Lean 4.17.0 on) a string literal is translated through the export's own
   [String.ofList] (or [String.mk]) and [Char.ofNat] (lean.ml, [string_lit_expr]); the BitVec [Char] needs
   no reflective constructor here. *)

(* Transport of proof arguments across Nat literals (README, "Transport of proof arguments across Nat
   literals"). Rocq computes Lean's Nat arithmetic on the unary [Nat] one [Nat_succ] at a time, so Lean
   Import proves an equality [x = y] of two closed Nat terms of equal value (a literal, a constant such as
   [UInt32.size], or [2 ^ 32] built from the export's own [Nat.pow]) through Rocq's binary [N] and casts an
   SProp argument along it with [sprop_transport]. The lemmas below are proved by induction on [Nat],
   [rewrite], [destruct] and [lia]: the [toN] lemmas rely on no axiom, [Nat_eq_of_toN] and
   [sprop_transport] only on the definitional UIP of [eq]. The importer instantiates them with the
   export's [Nat.add], [Nat.mul] and [Nat.pow], whose defining equations it closes by [Logic.eq_refl], and
   with steps that compute the value of a literal from its form. The lemmas of the Fin case (the two
   values of a [Fin] that two closed terms reduce to) do not go through [N]: each is [Logic.eq_refl] on
   the values, which the kernel computes on the unary [Nat], so the importer generates one only when the
   value and every operand of it but a divisor are below 65536. *)
Section nat_transport.
  Import ZArith NArith Lia.
  Local Unset Universe Polymorphism.

  Fixpoint toN (n : Nat) : N :=
    match n with
    | Nat_zero => N0
    | Nat_succ n => N.succ (toN n)
    end.

  Lemma toN_inj (a b : Nat) : Logic.eq (toN a) (toN b) -> Logic.eq a b.
  Proof.
    revert b; induction a as [|a IH]; intros [|b] H; cbn [toN] in H.
    - reflexivity.
    - exfalso; lia.
    - exfalso; lia.
    - f_equal; apply IH; lia.
  Qed.

  Lemma toN_double (n : Nat) : Logic.eq (toN (double n)) (N.double (toN n)).
  Proof.
    induction n as [|n IH]; cbn [double toN].
    - reflexivity.
    - rewrite IH, !N.double_spec; lia.
  Qed.

  (* For any [add], [mul] and [pow] that recurse on their second argument as Lean's [Nat.add],
     [Nat.mul] and [Nat.pow] do, given as their defining equations. *)
  Lemma toN_add (add : Nat -> Nat -> Nat)
    (add_0 : forall n, Logic.eq (add n Nat_zero) n)
    (add_S : forall n m, Logic.eq (add n (Nat_succ m)) (Nat_succ (add n m)))
    (a b : Nat) : Logic.eq (toN (add a b)) (N.add (toN a) (toN b)).
  Proof.
    induction b as [|b IH].
    - rewrite add_0; cbn [toN]; lia.
    - rewrite add_S; cbn [toN]; rewrite IH; lia.
  Qed.

  Lemma toN_mul (add mul : Nat -> Nat -> Nat)
    (Hadd : forall a b, Logic.eq (toN (add a b)) (N.add (toN a) (toN b)))
    (mul_0 : forall n, Logic.eq (mul n Nat_zero) Nat_zero)
    (mul_S : forall n m, Logic.eq (mul n (Nat_succ m)) (add (mul n m) n))
    (a b : Nat) : Logic.eq (toN (mul a b)) (N.mul (toN a) (toN b)).
  Proof.
    induction b as [|b IH].
    - rewrite mul_0; cbn [toN]; lia.
    - rewrite mul_S, Hadd, IH; cbn [toN]; now rewrite N.mul_succ_r.
  Qed.

  Lemma toN_pow (mul pow : Nat -> Nat -> Nat)
    (Hmul : forall a b, Logic.eq (toN (mul a b)) (N.mul (toN a) (toN b)))
    (pow_0 : forall b, Logic.eq (pow b Nat_zero) (Nat_succ Nat_zero))
    (pow_S : forall b e, Logic.eq (pow b (Nat_succ e)) (mul (pow b e) b))
    (a b : Nat) : Logic.eq (toN (pow a b)) (N.pow (toN a) (toN b)).
  Proof.
    induction b as [|b IH].
    - now rewrite pow_0.
    - rewrite pow_S, Hmul, IH; cbn [toN].
      rewrite (N.pow_succ_r _ _ (N.le_0_l _)).
      apply N.mul_comm.
  Qed.

  (* The steps of a certificate [Logic.eq (toN t) w] for a closed Nat term [t] and a binary literal [w]:
     each step states its term as it is, so that the kernel compares a step with the next one term for
     term, and checks each binary computation ([E]) on literals. *)
  Lemma toN_succ_step (m : Nat) (v w : N) (H : Logic.eq (toN m) v) (E : Logic.eq (N.succ v) w)
    : Logic.eq (toN (Nat_succ m)) w.
  Proof. cbn [toN]; rewrite H; exact E. Qed.

  Lemma toN_double_step (m : Nat) (v w : N) (H : Logic.eq (toN m) v) (E : Logic.eq (N.double v) w)
    : Logic.eq (toN (double m)) w.
  Proof. rewrite toN_double, H; exact E. Qed.

  (* [Hab] is closed by [Logic.eq_refl]: [b] is what [a] unfolds to (the body of a constant, or the
     literal of an [OfNat.ofNat]). *)
  Lemma toN_unfold_step (a b : Nat) (w : N) (Hab : Logic.eq a b) (H : Logic.eq (toN b) w)
    : Logic.eq (toN a) w.
  Proof. rewrite Hab; exact H. Qed.

  (* [f] is the operation as the term applies it ([HPow.hPow Nat Nat Nat inst], say), [g] the export's
     operation ([Nat.pow]), [Hfg] closed by [Logic.eq_refl] on open [a b], [Hg] one of the lemmas above. *)
  Lemma toN_op_step (f g : Nat -> Nat -> Nat) (h : N -> N -> N)
    (Hfg : forall a b, Logic.eq (f a b) (g a b))
    (Hg : forall a b, Logic.eq (toN (g a b)) (h (toN a) (toN b)))
    (a b : Nat) (va vb w : N) (Ha : Logic.eq (toN a) va) (Hb : Logic.eq (toN b) vb)
    (E : Logic.eq (h va vb) w) : Logic.eq (toN (f a b)) w.
  Proof. rewrite Hfg, Hg, Ha, Hb; exact E. Qed.

  Lemma Nat_eq_of_toN (x y : Nat) (w : N) (Hx : Logic.eq (toN x) w) (Hy : Logic.eq (toN y) w)
    : @eq@{Set} Nat x y.
  Proof.
    assert (H : Logic.eq x y) by exact (toN_inj x y (Logic.eq_trans Hx (Logic.eq_sym Hy))).
    destruct H; constructor.
  Qed.

  Definition sprop_transport (P : Nat -> SProp) {x y : Nat} (e : @eq@{Set} Nat x y) (p : P x) : P y.
  Proof. destruct e; exact p. Defined.

  Register N.add as lean.N.add.
  Register N.mul as lean.N.mul.
  Register N.pow as lean.N.pow.
End nat_transport.

Register toN_succ_step as lean.toN_succ_step.
Register toN_double_step as lean.toN_double_step.
Register toN_unfold_step as lean.toN_unfold_step.
Register toN_op_step as lean.toN_op_step.
Register toN_add as lean.toN_add.
Register toN_mul as lean.toN_mul.
Register toN_pow as lean.toN_pow.
Register Nat_eq_of_toN as lean.Nat_eq_of_toN.
Register sprop_transport as lean.sprop_transport.
