import Init

set_option maxRecDepth 4096

namespace RLI434SW

private theorem lt7 : 7 < UInt32.size := by decide
private theorem lt127 : 127 < UInt32.size := by decide

def plain (n : Nat) (h : n < UInt32.size) : UInt32 := UInt32.ofNatLT n h
def wrapped (n : Nat) (h : n < UInt32.size) : UInt32 := id (UInt32.ofNatLT n h)

theorem ordinary (v : UInt32) (h : v ≤ plain 127 lt127) : v ≤ 127 := h

-- W03b: instantiate a type parameter before reducing to the Fin constructor.
macro "repeatSucc " n:num t:term : term => do
  let mut e := t
  for _ in [:n.getNat] do e ← `(Nat.succ $e)
  return e

def poly.{u} (α : Type u) (_ : Nat) : UInt32 :=
  (fun (_ : α → α) (_ : Nat) => plain 7 lt7) (fun x => x) (Nat.add 0 (repeatSucc 320 0))
theorem poly_body (v : UInt32) (h : v ≤ poly PUnit.{2} (Nat.add 0 0)) : v ≤ 7 := h

def atWidth (w : Nat) (n : Nat) (h : n < 2 ^ w) : BitVec w := BitVec.ofNatLT n h
def atWidth' (w : Nat) (n : Nat) (h : n < 2 ^ w) : BitVec w := id (BitVec.ofNatLT n h)

-- Nat.add x 0 is closed under the lambda passed to fnA or fnB.
-- It is open inside the application of openA or openB, viewed on its own.
-- The open pair uses another value so it cannot reuse the closed pair's lemma.
def fnA (_ : Nat → Nat) : UInt32 := plain 7 lt7
def fnB (_ : Nat → Nat) : UInt32 := 7
def openA (_ : Nat) : UInt32 := UInt32.ofNatLT 8 (by decide)
def openB (_ : Nat) : UInt32 := UInt32.ofNatLT (Nat.add 3 5) (by decide)

theorem binder_depth (v : UInt32)
    (h : v ≤ fnA (fun x : Nat => Nat.add x 0) ∧ (∀ x : Nat, v ≤ openA (Nat.add x 0))) :
    v ≤ fnB (fun x : Nat => Nat.add x 0) ∧ (∀ x : Nat, v ≤ openB (Nat.add x 0)) := h

def widthA : Nat := repeatSucc 64 0
def widthB : Nat := repeatSucc 64 0

theorem parameters_equal (v : BitVec (repeatSucc 64 0))
    (h : v = atWidth (repeatSucc 64 0) 7 (by decide)) :
    v = atWidth' (repeatSucc 64 0) (3 + 4) (by decide) := h

theorem parameters_differ (v : BitVec widthA) (h : v = atWidth widthA 7 (by decide)) :
    v = atWidth' widthB (3 + 4) (by decide) := h

-- W10a/d: zeta and beta both duplicate the inserted term. Beta leaves a
-- partially applied head and must join the old and new argument arrays.

-- The visible hole uses the literal returned by the discarder, not its inputs.
def drop2 (_ _ : Nat) : UInt32 := plain 7 lt7

def beta_drop (n : Nat) : UInt32 := (fun x : Nat => drop2 x x) (repeatSucc 320 n)
def let_drop (n : Nat) : UInt32 := let x := repeatSucc 320 n; drop2 x x

-- The argument Nat.add 0 0 of the side under test is a trigger of the entry's first scan.
theorem beta_subst (v : UInt32) (h : v ≤ beta_drop (Nat.add 0 0)) : v ≤ 7 := h
theorem let_subst (v : UInt32) (h : v ≤ let_drop (Nat.add 0 0)) : v ≤ 7 := h

macro "natArgs " n:num f:term : term => do
  let mut e := f
  for _ in [:n.getNat] do e ← `($e (0 : Nat))
  return e

macro "natLams " n:num e:term : term => do
  let mut body := e
  for _ in [:n.getNat] do body ← `(fun _ : Nat => $body)
  return body

-- W10b: declining the wide pair must leave the other argument's cast intact.
-- The first pair is convertible cheaply even when the optional pass declines it.
-- wideA's head takes 96 binders, more than the 64 steps a side may take. Its body names the first binder at
-- sixteen places, and that binder's argument is a run of 320 successors: a check after the substitution of
-- all the binders would pay for fifteen copies of the run.
def drop16 (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ : Nat) : UInt32 := plain 7 lt7
def wideA (_ : Nat) : UInt32 :=
  natArgs 95 ((fun x : Nat => natLams 95 (drop16 x x x x x x x x x x x x x x x x)) (repeatSucc 320 0))
def wideB (_ : Nat) : UInt32 := plain 7 lt7

theorem early_cap (v : UInt32) (h₁ : v ≤ wideA 0) (h₂ : v ≤ plain 127 lt127) :
    v ≤ wideB 0 ∧ v ≤ 127 := And.intro h₁ h₂

def wide_apply (_ : Nat) : UInt32 := natArgs 47 ((fun _ : Nat => (natLams 48 (plain 7 lt7)) 0) 0)
theorem flatten (v : UInt32) (h : v ≤ wide_apply (Nat.add 0 0)) : v ≤ 7 := h

-- W14b: looking at this head's result requires peeling all its binders.
def long_head := natLams 48 (plain 7 lt7)
theorem product_peel (v : UInt32) (h : v ≤ (7 : UInt32)) :
    v ≤ natArgs 47 (long_head (Nat.add 0 0)) := h

-- W26a: the export contains only linear syntax. Each head contraction
-- duplicates the current replacement eight times. The last step discards it.
def fan (a b c d e f g h : Nat) : Nat := a + b + c + d + e + f + g + h

-- Keep the let chain at the head so that optional head exposure creates the DAG.
macro "headStages " n:num t:term : term => do
  let y := Lean.mkIdent `y
  let mut body ← `(drop2 $y:ident $y:ident)
  for _ in [:n.getNat] do
    body ← `(let $y:ident := fan $y:ident $y:ident $y:ident $y:ident $y:ident $y:ident $y:ident $y:ident; $body)
  `(let $y:ident := $t; $body)

def finite_head (n : Nat) : UInt32 := headStages 2 n
def huge_head (n : Nat) : UInt32 := headStages 24 n

theorem head_fits (v : UInt32) (h : v ≤ finite_head (Nat.add 0 0)) : v ≤ 7 := h

-- The other Fin pair compares UInt8 values: without the stop it would cast, and the kernel converts it at
-- once, so the kernel checks Lean's original value within the test's entry limit.
private theorem lt127b : 127 < UInt8.size := by decide
def plain8 (n : Nat) (h : n < UInt8.size) : UInt8 := UInt8.ofNatLT n h

-- This preserves the original proof after a stop; the other Fin pair would cast.
theorem head_overflow (v : UInt32) (w : UInt8) (h : v ≤ huge_head (Nat.add 0 0))
    (h' : w ≤ plain8 127 lt127b) : v ≤ wideB 0 ∧ w ≤ 127 := And.intro h h'

-- W14b: the long head of product_peel in the expected type of an argument, not of the result. The result walk's
-- gate (the entry's own part) reads no such type here, so the argument's gate is the first to peel the head's
-- product chain, in the argument's own part, which is the entry's largest part.
def consumeLong (v : UInt32) (_ : v ≤ natArgs 47 (long_head (Nat.add 0 0))) : Nat := v.toNat
def product_peel_arg (v : UInt32) (h : v ≤ (7 : UInt32)) : Nat := consumeLong v h

end RLI434SW
