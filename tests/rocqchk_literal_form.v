From Stdlib Require Import NArith.
From LeanImport Require Import Lean.

(* The library tests/rocqchk_literal_below.v, tests/rocqchk_literal.v and tests/rocqchk_literal_over.v load: the term
   the importer writes for a literal v of 5000 or more (README, "Natural number literals"; src/leanNatTransport.ml,
   large_literal), written out from that rule alone: Nat_succ applied r times (r = 1 + (v - 5) mod 8) to the binary
   form of v - r, where the binary form of 0 is Nat_zero, of 2k is double applied to that of k, and of 2k + 1 is
   Nat_succ of that. A test defines the form of its value with Eval cbv -[double], so that conversion compares the
   imported constant with it term for term, without unfolding double. *)
Fixpoint rocqchk_bin (p : positive) : Nat :=
  match p with
  | xH => Nat_succ (LeanImport.Lean.double Nat_zero)
  | xO p => LeanImport.Lean.double (rocqchk_bin p)
  | xI p => Nat_succ (LeanImport.Lean.double (rocqchk_bin p))
  end.

Fixpoint rocqchk_succs (k : nat) (c : Nat) : Nat :=
  match k with
  | O => c
  | S k => Nat_succ (rocqchk_succs k c)
  end.

Definition rocqchk_lit (v : N) : Nat :=
  let r := N.to_nat (1 + (v - 5) mod 8) in
  match (v - N.of_nat r)%N with
  | N0 => rocqchk_succs r Nat_zero
  | Npos p => rocqchk_succs r (rocqchk_bin p)
  end.
