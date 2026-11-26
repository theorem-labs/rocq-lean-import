import Init

set_option maxRecDepth 4096

namespace RLI434W

macro "succs " n:num t:term : term => do
  let mut e := t
  for _ in [:n.getNat] do e ← `(Nat.succ $e)
  return e

macro "adds " n:num k:num t:term : term => do
  let k : Lean.TSyntax `term := ⟨k.raw⟩
  let mut e := t
  for _ in [:n.getNat] do e ← `(Nat.add $k $e)
  return e

-- W03a: the universe occurs in the body, not in the declared Nat type.
def polyNat.{u} : Nat := (fun _ : Type u => adds 96 0 4096) PUnit.{u+1}
theorem poly_nat (n : Nat) (h : n = polyNat.{1}) : n = 4096 := h

-- W02: use HAdd.hAdd at distinct universes as well as at distinct dictionaries.
local instance : HAdd (ULift.{1,0} Nat) (ULift.{1,0} Nat) (ULift.{1,0} Nat) :=
  ⟨fun a b => ⟨Nat.add a.down b.down⟩⟩
theorem instances (n : Nat) (v : ULift.{1,0} Nat) (h : n = 4091 + 5 ∧ v = v + ULift.up 0) :
    n = 4096 ∧ v = v + ULift.up 0 := h

-- W06a: the Rocq test occupies generated names 1 and 2 before this import.
theorem names (n : Nat) (h : n = Nat.add 4095 1) : n = 4096 := h

-- W06b/W07/W09c: the equal Nat applications in equal_nodes are separately
-- translated. The only lemma needed there is the one for the second conjunct.
theorem endpoints (n : Nat) (h : n = adds 96 0 4096) : n = 4096 := h

theorem cache_hit (n : Nat) (h : n = adds 96 0 4096) : n = 4096 := h

theorem cache_miss (n : Nat) (h : n = adds 96 0 4097) : n = 4097 := h

theorem equal_nodes (n : Nat) (h : n = (adds 96 0 4096) ∧ n = Nat.add 4094 2) :
    n = (adds 96 0 4096) ∧ n = 4096 := h

private theorem lt7 : 7 < UInt32.size := by decide
private theorem lt8 : 8 < UInt32.size := by decide
private theorem lt127 : 127 < UInt32.size := by decide

def u7 (_ : Nat) : UInt32 := UInt32.ofNatLT 7 lt7
def u8 (_ : Nat) : UInt32 := UInt32.ofNatLT 8 lt8

-- W12/W15/W26c: distinct Nat and Fin holes, then a duplicate Fin hole.
-- The second Fin cast lifts the proof containing the two earlier casts.
theorem motives (v : UInt32) (n : Nat)
    (h : (n = Nat.add 4093 3) ∧ (v ≤ u7 0) ∧ (v ≤ u8 0) ∧ (v ≤ u7 0)) :
    (n = 4096) ∧ (v ≤ 7) ∧ (v ≤ 8) ∧ (v ≤ 7) := h

def proofArg (v : UInt32) (_ : v ≤ 127) : Nat := v.toNat

def Dep (v : UInt32) := (h : v ≤ 127) → Nat

def viaAlias (v : UInt32) : Dep v := proofArg v

def depArgs (v : UInt32) (n : Nat) (_ : n = 4096) : Dep v := proofArg v

def dependent (v : UInt32) (n : Nat) (hn : n = Nat.add 4092 4)
    (hv : v ≤ UInt32.ofNatLT 127 lt127) : Nat := depArgs v n hn hv

def alias_product (v : UInt32) (hv : v ≤ UInt32.ofNatLT 127 lt127) : Nat := viaAlias v hv

-- The declined rows compare UInt8 values, which the kernel converts at once (row F7h), so it checks Lean's
-- value within the test's entry limit. The argument Nat.add 0 0 is a trigger of the entry's first scan.
private theorem lt7b : 7 < UInt8.size := by decide

def w7 (_ : Nat) : UInt8 := UInt8.ofNatLT 7 lt7b

-- W18/W19: the kernel can reduce the match; the optional type query declines.
def MatchFn (b : Bool) (v : UInt8) : Type :=
  match b with
  | true => (v ≤ (7 : UInt8)) → Nat
  | false => Nat

def matched (v : UInt8) : MatchFn true v := fun _ => v.toNat

def computed_head (v : UInt8) (h : v ≤ w7 (Nat.add 0 0)) : Nat := matched v h

def MatchProof (b : Bool) (v : UInt8) : Prop :=
  match b with
  | true => v ≤ w7 0
  | false => False

theorem proofOfMatch (v : UInt8) (h : v ≤ w7 0) : MatchProof true v := h

def smallProofArg (v : UInt8) (_ : v ≤ (7 : UInt8)) : Nat := v.toNat

def computed_arg (v : UInt8) (h : v ≤ w7 (Nat.add 0 0)) : Nat := smallProofArg v (proofOfMatch v h)

-- This puts the computed product in the type of an actual proof application.
def MatchProofFn (b : Bool) (v : UInt8) : Prop :=
  match b with
  | true => (v ≤ w7 0) → (v ≤ w7 0)
  | false => True

def computed_arg_product (v : UInt8) (p : MatchProofFn true v) (h : v ≤ w7 (Nat.add 0 0)) : Nat :=
  smallProofArg v (p h)

-- W17: a beta redex in the expected type carries the transport site.
def betaArg (v : UInt32) (_ : (fun k : UInt32 => v ≤ k) (127 : UInt32)) : Nat := v.toNat

def beta_normalize (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 lt127) : Nat := betaArg v h

-- W20a: the declared and actual result differ behind many leading binders.
macro "binders " n:num body:term : term => do
  let mut e := body
  for _ in [:n.getNat] do e ← `(Nat → $e)
  return e

macro "lambdas " n:num body:term : term => do
  let mut e := body
  for _ in [:n.getNat] do e ← `(fun _ : Nat => $e)
  return e

theorem result_binders (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 lt127) :
    binders 80 (v ≤ 127) := lambdas 80 h

-- W14a: a distinct constructor has a long declared product type.
inductive Wide where
  | mk : binders 80 Wide

theorem global_type (n : Nat) (k : binders 80 Wide)
    (h : k = Wide.mk ∧ n = Nat.add 4090 6) : k = Wide.mk ∧ n = 4096 := h

def ResultFamily (b : Bool) : Type := match b with | true => Prop | false => Nat

def resultAt (b : Bool) (v x : UInt8) : ResultFamily b :=
  match b with
  | true => v ≤ x
  | false => Nat.zero

theorem computed_sort (v : UInt8) (h : resultAt true v (w7 (Nat.add 0 0))) : resultAt true v 7 := h

-- W24a: the differing tails are below the bounded hash prefix. Query the
-- resulting A and B in one Fin reader, with A physically reused after beta.
def aba (a b : Nat) (h : Nat.add a (Nat.add b a) < UInt32.size) : UInt32 :=
  UInt32.ofNatLT (Nat.add a (Nat.add b a)) h

theorem collision_aba (v : UInt32)
    (h : v ≤ aba (adds 24 0 1) (adds 24 0 2) (by decide)) : v ≤ (4 : UInt32) := h

theorem collision_fresh (v : UInt32)
    (h : v ≤ aba (adds 24 0 2) (adds 24 0 1) (by decide)) : v ≤ (5 : UInt32) := h

-- W24b: distinct, nonunary suffixes. Each prefix adds one to the preceding value. After a budget stop the
-- kernel's conversion of Lean's value outlasts the test's 20 s entry limit, which the stop cases assert.
theorem collision_chain (v : UInt8)
    (h : v ≤ UInt8.ofNatLT (adds 180 1 1) (by decide)) : v ≤ (181 : UInt8) := h

-- W25: do not peel the unary Nat.succ heads (two runs of 512 under Nat.add), but visit the application
-- of a different unary head, callback, with its irrelevant argument.
def callback (_ : (0 : UInt32) ≤ 127) : Nat := 23

def nested_cast (h : (0 : UInt32) ≤ UInt32.ofNatLT 127 lt127) : Nat :=
  Nat.add (succs 512 (callback h)) (succs 512 0)

-- W26b: the input is linear in the number of redexes. Each contraction
-- inserts the same closed application into eight positions.
def fan (a b c d e f g h : Nat) : Nat := a + b + c + d + e + f + g + h

macro "redexes " n:num t:term : term => do
  let mut e := t
  for _ in [:n.getNat] do e ← `((fun x : Nat => fan x x x x x x x x) $e)
  return e

def ignoreNat (_ : Nat) : Nat := 0

def consumeFit (v : UInt32) (_ : v ≤ 127 ∧ ignoreNat (redexes 2 0) = 0) : Nat := v.toNat
def consumeHuge (v : UInt32) (_ : v ≤ 127 ∧ ignoreNat (redexes 24 0) = 0) : Nat := v.toNat

def normalize_fits (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 lt127 ∧ (0 : Nat) = 0) : Nat :=
  consumeFit v h
def normalize_overflow (v : UInt32) (h : v ≤ (127 : UInt32) ∧ Nat.add 0 0 = 0) : Nat :=
  consumeHuge v h

-- The let substitutes an application, not a constant, into both operands.
def sharedSome (_ : Nat) : UInt32 :=
  let y := adds 96 0 3
  UInt32.ofNatLT (Nat.add y y) (by decide)
theorem shared_some (v : UInt32) (h : v ≤ sharedSome (Nat.add 0 0)) : v ≤ (6 : UInt32) := h

-- The nonconstant Nat.sub has no optional Nat value. A dependent argument
-- substitution supplies that same application to both operands of Nat.add.
def observeNone (v : UInt32) (x : Nat)
    (_ : Nat.add x x = 0) (_ : v ≤ (127 : UInt32)) : Nat := v.toNat
def shared_none (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 lt127) : Nat :=
  observeNone v (Nat.sub (adds 96 0 3) 3) rfl h

-- Rows whose mutant drops a charge of the entry's own part (W02's instance collection, W14a, W16, W18/W19a,
-- W20a). The cases above pin their stop on the larger argument part, which such a mutant leaves as it is; in
-- each entry below the entry's own part is the largest part, so a stop one step below it is decided by the
-- entry's own charges. The hypothesis _b holds a ballast term that only the entry's own scan and walk read: it
-- is in the statement and in a binder type of the value, and in no argument the pass casts. The Fin hole
-- compares UInt8 values, so a cast is cheap and, after a budget stop, the kernel converts Lean's value at once
-- (row F7h); Nat.add 0 0 or 4 + 3 is a trigger of the entry's first scan.
macro "ballast" : term =>
  `(fan (succs 500 0) (succs 500 0) (succs 500 0) (succs 500 0) (succs 500 0) (succs 500 0) (succs 500 0)
      (succs 500 0))

private theorem lt7c : 4 + 3 < UInt8.size := by decide

-- W02: the Fin value 4 + 3 reads HAdd.hAdd at Nat's instance, which the entry's view of the export collects
-- with the instance of the second universe (the local ULift instance above).
theorem instances_own (v : UInt8) (u : ULift.{1,0} Nat) (_b : ignoreNat ballast = 0)
    (h : v ≤ UInt8.ofNatLT (4 + 3) lt7c ∧ u = u + ULift.up 0) : v ≤ 7 ∧ u = u + ULift.up 0 := h

-- W14a: the first scan reads the long declared type of the constructor Wide.mk once.
theorem global_type_own (v : UInt8) (k : binders 80 Wide) (_b : ignoreNat ballast = 0)
    (h : k = Wide.mk ∧ v ≤ w7 (Nat.add 0 0)) : k = Wide.mk ∧ v ≤ 7 := h

def Dep8 (v : UInt8) := (h : v ≤ (7 : UInt8)) → Nat

-- W16: a dependent domain (substituted for hw), a non-product codomain Dep8 v (exposed after the
-- substitution of the arguments before it), and the first copy of the argument array at hw's cast.
def depOwn (v w : UInt8) (_ : w ≤ (7 : UInt8)) : Dep8 v := smallProofArg v

def dependent_own (v w : UInt8) (_b : ignoreNat ballast = 0) (hw : w ≤ w7 (Nat.add 0 0))
    (hv : v ≤ w7 (Nat.add 0 0)) : Nat := depOwn v w hw hv

-- W18/W19a: the head's type is read, and its product exposed through the transparent alias Dep8.
def viaAlias8 (v : UInt8) : Dep8 v := smallProofArg v

def alias_own (v : UInt8) (_b : ignoreNat ballast = 0) (hv : v ≤ w7 (Nat.add 0 0)) : Nat := viaAlias8 v hv

-- W20a: the result's proof is under 80 leading binders, which the result walk descends.
theorem result_own (v : UInt8) (_b : ignoreNat ballast = 0) (h : v ≤ w7 (Nat.add 0 0)) :
    binders 80 (v ≤ 7) := lambdas 80 h

end RLI434W
