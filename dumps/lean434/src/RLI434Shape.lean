/- The shapes of the Fin case of the transport pass (tests/fin_transport_shape.v): each theorem passes a proof of
   `v ≤ a` where `v ≤ d` is expected, `a` and `d` closed terms that reduce to the same value. -/

namespace RLI434S

/- The basic cast: `UInt32.ofNatLT 127 _` against `(127 : UInt32)`, whose Fin values are 127 and 127 % 2 ^ 32. -/
theorem cast_127 (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ 127 := h

/- The result position: the theorem's own value, `rfl`, has the type `a = a` where `a = 127` is declared. -/
theorem result_127 : UInt32.ofNatLT 127 (by decide) = (127 : UInt32) := rfl

/- One argument with a Fin hole and a Nat hole. -/
theorem fin_and_nat (v : UInt32) (n : Nat) (h : v ≤ UInt32.ofNatLT 127 (by decide) ∧ n < 4095 + 1) :
    v ≤ 127 ∧ n < 4096 := h

/- Records of one field above the Fin: Int32 over UInt32 over BitVec 32 (3), W4 over those (4), W5 over W4 (5). -/
theorem chain_3 (v : Int32) (h : v ≤ (UInt32.ofNatLT 127 (by decide)).toInt32) : v ≤ Int32.ofNat 127 := h

structure W4 where
  val : Int32

def W4.ofA (x : UInt32) : W4 := ⟨x.toInt32⟩
def W4.ofB (n : Nat) : W4 := ⟨Int32.ofNat n⟩

theorem chain_4 (v : W4) (h : v = W4.ofA (UInt32.ofNatLT 127 (by decide))) : v = W4.ofB 127 := h

structure W5 where
  val : W4

def W5.ofA (x : UInt32) : W5 := ⟨W4.ofA x⟩
def W5.ofB (n : Nat) : W5 := ⟨W4.ofB n⟩

/- A side may take 64 steps: an unfolding, the substitution of one bound argument, a zeta step and a projection
   count one each. a = g27 h takes 63 (two per gi, three for UInt32.ofNatLT 127 h, four for BitVec.ofNatLT),
   ge27 h one more (ge27 := g27 binds nothing), g28 h 65. -/
def g0 (h : 127 < UInt32.size) : UInt32 := UInt32.ofNatLT 127 h
def g1 (h : 127 < UInt32.size) : UInt32 := g0 h
def g2 (h : 127 < UInt32.size) : UInt32 := g1 h
def g3 (h : 127 < UInt32.size) : UInt32 := g2 h
def g4 (h : 127 < UInt32.size) : UInt32 := g3 h
def g5 (h : 127 < UInt32.size) : UInt32 := g4 h
def g6 (h : 127 < UInt32.size) : UInt32 := g5 h
def g7 (h : 127 < UInt32.size) : UInt32 := g6 h
def g8 (h : 127 < UInt32.size) : UInt32 := g7 h
def g9 (h : 127 < UInt32.size) : UInt32 := g8 h
def g10 (h : 127 < UInt32.size) : UInt32 := g9 h
def g11 (h : 127 < UInt32.size) : UInt32 := g10 h
def g12 (h : 127 < UInt32.size) : UInt32 := g11 h
def g13 (h : 127 < UInt32.size) : UInt32 := g12 h
def g14 (h : 127 < UInt32.size) : UInt32 := g13 h
def g15 (h : 127 < UInt32.size) : UInt32 := g14 h
def g16 (h : 127 < UInt32.size) : UInt32 := g15 h
def g17 (h : 127 < UInt32.size) : UInt32 := g16 h
def g18 (h : 127 < UInt32.size) : UInt32 := g17 h
def g19 (h : 127 < UInt32.size) : UInt32 := g18 h
def g20 (h : 127 < UInt32.size) : UInt32 := g19 h
def g21 (h : 127 < UInt32.size) : UInt32 := g20 h
def g22 (h : 127 < UInt32.size) : UInt32 := g21 h
def g23 (h : 127 < UInt32.size) : UInt32 := g22 h
def g24 (h : 127 < UInt32.size) : UInt32 := g23 h
def g25 (h : 127 < UInt32.size) : UInt32 := g24 h
def g26 (h : 127 < UInt32.size) : UInt32 := g25 h
def g27 (h : 127 < UInt32.size) : UInt32 := g26 h
def g28 (h : 127 < UInt32.size) : UInt32 := g27 h
def ge27 := g27

theorem side_63 (v : UInt32) (h : v ≤ g27 (by decide)) : v ≤ 127 := h
theorem side_64 (v : UInt32) (h : v ≤ ge27 (by decide)) : v ≤ 127 := h
theorem side_65 (v : UInt32) (h : v ≤ g28 (by decide)) : v ≤ 127 := h

/- An open pair: `n` and `hn` are bound. -/
def ofNatLT2 (n : Nat) (h : n < UInt32.size) : UInt32 := UInt32.ofNatLT n h

theorem open_pair (n : Nat) (hn : n < UInt32.size) (v : UInt32) (h : v ≤ UInt32.ofNatLT n hn) :
    v ≤ ofNatLT2 n hn := h

/- A pair whose type is a record of two fields. -/
def pa (n : Nat) : Nat × Nat := (127, n)
def pb (n : Nat) : Nat × Nat := (127, n)

theorem two_fields (p : Nat × Nat) (h : p = pa UInt32.size) : p = pb UInt32.size := h

/- Equal values at other parameters: the expected side at the width 31 + 1, under `id`. -/
theorem other_width (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) :
    v ≤ id (UInt32.ofBitVec (BitVec.ofFin (w := 31 + 1) ⟨127 % 2 ^ (31 + 1), Nat.mod_lt _ (by decide)⟩)) := h

/- Five records: no hole. -/
theorem chain_5 (v : W5) (h : v = W5.ofA (UInt32.ofNatLT 127 (by decide))) : v = W5.ofB 127 := h

/- A value the pass does not compute: 200 - 73. -/
theorem sub_value (v : UInt32) (h : v ≤ UInt32.ofNatLT (200 - 73) (by decide)) : v ≤ 127 := h

/- A side that is a constant applied to nothing: no Fin site (the gate looks for applications only). -/
def lit127 : UInt32 := 127
theorem gate_const (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ lit127 := h

/- Where head reduction stops, each side an application (5000 makes the pass look at the entry). An axiom,
   after one unfolding: -/
axiom axU : UInt32
noncomputable def viaAx (_ : Nat) : UInt32 := axU
noncomputable def viaAx2 (_ : Nat) : UInt32 := axU
theorem stop_axiom (v : UInt32) (h : v ≤ viaAx 5000) : v ≤ viaAx2 5000 := h

/- An opaque definition, after one unfolding: -/
opaque opqU : UInt32
def viaOpq (_ : Nat) : UInt32 := opqU
def viaOpq2 (_ : Nat) : UInt32 := opqU
theorem stop_opaque (v : UInt32) (h : v ≤ viaOpq 5000) : v ≤ viaOpq2 5000 := h

/- A match (`if`), a fixpoint (structural recursion) and a projection of a match, each equal to 127: -/
def viaIte (_ : Nat) : UInt32 := if (1 : Nat) < 2 then 127 else 127
theorem stop_match (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ viaIte 0 := h

def rep : Nat → UInt32
  | 0 => 127
  | n + 1 => rep n
theorem stop_fix (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ rep 2 := h

def pairU : UInt32 × Nat := if (1 : Nat) < 2 then (127, 0) else (127, 1)
def projU (_ : Nat) : UInt32 := pairU.1
theorem stop_proj (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ projU 0 := h

/- A let on the way, which head reduction passes (zeta): -/
def withLet (_ : Nat) : UInt32 := let x : UInt32 := 127; x
theorem step_let (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ withLet 0 := h

/- A divisor of zero (127 % 0 = 127), and a divisor the pass does not compute (999, as 1000 - 1): -/
theorem mod_zero (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) :
    v ≤ id (UInt32.ofNatLT (127 % 0) (by decide)) := h

def sub1 (x : Nat) : Nat := x - 1
theorem mod_novalue (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) :
    v ≤ id (UInt32.ofNatLT (127 % sub1 1000) (by decide)) := h

/- Functions of three arguments, each applied to three: four steps per ti; t13 0 0 h takes 63, te13 (:= t13)
   64, tee13 (:= te13) 65. -/
def t0 (_ _ : Nat) (h : 127 < UInt32.size) : UInt32 := UInt32.ofNatLT 127 h
def t1 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t0 x y h
def t2 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t1 x y h
def t3 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t2 x y h
def t4 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t3 x y h
def t5 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t4 x y h
def t6 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t5 x y h
def t7 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t6 x y h
def t8 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t7 x y h
def t9 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t8 x y h
def t10 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t9 x y h
def t11 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t10 x y h
def t12 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t11 x y h
def t13 (x y : Nat) (h : 127 < UInt32.size) : UInt32 := t12 x y h
def te13 := t13
def tee13 := te13

theorem bind3_63 (v : UInt32) (h : v ≤ t13 0 0 (by decide)) : v ≤ 127 := h
theorem bind3_64 (v : UInt32) (h : v ≤ te13 0 0 (by decide)) : v ≤ 127 := h
theorem bind3_65 (v : UInt32) (h : v ≤ tee13 0 0 (by decide)) : v ≤ 127 := h

/- Steps in the subject of a projection: prj19 x is (pq19 x).1, pq19 a chain of definitions down to the pair
   (127, 0); d = prj19 0 takes 63 steps, prje19 0 (prje19 := prj19) 64, prj20 0 65. -/
def pq0 (_ : Nat) : UInt32 × Nat := (127, 0)
def pq1 (x : Nat) : UInt32 × Nat := pq0 x
def pq2 (x : Nat) : UInt32 × Nat := pq1 x
def pq3 (x : Nat) : UInt32 × Nat := pq2 x
def pq4 (x : Nat) : UInt32 × Nat := pq3 x
def pq5 (x : Nat) : UInt32 × Nat := pq4 x
def pq6 (x : Nat) : UInt32 × Nat := pq5 x
def pq7 (x : Nat) : UInt32 × Nat := pq6 x
def pq8 (x : Nat) : UInt32 × Nat := pq7 x
def pq9 (x : Nat) : UInt32 × Nat := pq8 x
def pq10 (x : Nat) : UInt32 × Nat := pq9 x
def pq11 (x : Nat) : UInt32 × Nat := pq10 x
def pq12 (x : Nat) : UInt32 × Nat := pq11 x
def pq13 (x : Nat) : UInt32 × Nat := pq12 x
def pq14 (x : Nat) : UInt32 × Nat := pq13 x
def pq15 (x : Nat) : UInt32 × Nat := pq14 x
def pq16 (x : Nat) : UInt32 × Nat := pq15 x
def pq17 (x : Nat) : UInt32 × Nat := pq16 x
def pq18 (x : Nat) : UInt32 × Nat := pq17 x
def pq19 (x : Nat) : UInt32 × Nat := pq18 x
def pq20 (x : Nat) : UInt32 × Nat := pq19 x
def prj19 (x : Nat) : UInt32 := (pq19 x).1
def prje19 := prj19
def prj20 (x : Nat) : UInt32 := (pq20 x).1

theorem proj_63 (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ prj19 0 := h
theorem proj_64 (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ prje19 0 := h
theorem proj_65 (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ prj20 0 := h

/- Chains of no record (a bare Fin, at small values and with a Nat of 4096 or more) and of one (BitVec alone). -/
def fin383 (_ : Nat) : Fin 256 := Fin.ofNat 256 383
theorem chain_0_small (v : Fin 256) (h : v ≤ Fin.ofNat 256 127) : v ≤ fin383 0 := h

def fin12292 (_ : Nat) : Fin 8192 := Fin.ofNat 8192 12292
theorem chain_0 (v : Fin 8192) (h : v ≤ Fin.ofNat 8192 4100) : v ≤ fin12292 0 := h

theorem chain_1 (v : BitVec 32) (h : v ≤ BitVec.ofNatLT 127 (by decide)) : v ≤ 127 := h

/- Beta at a lambda head: the let (one zeta step) leaves (fun _ .. _ => g24 h) 0 .. 0 at the head of the side, and
   head reduction substitutes one argument per binder (one step each) before it unfolds g24 (57 steps): lam3 takes
   63 steps, lam4 64, lam5 65. -/
def lam3 (h : 127 < UInt32.size) : UInt32 := let f := fun (_ _ _ : Nat) => g24 h; f 0 0 0
def lam4 (h : 127 < UInt32.size) : UInt32 := let f := fun (_ _ _ _ : Nat) => g24 h; f 0 0 0 0
def lam5 (h : 127 < UInt32.size) : UInt32 := let f := fun (_ _ _ _ _ : Nat) => g24 h; f 0 0 0 0 0
theorem lam_63 (v : UInt32) (h : v ≤ lam3 (by decide)) : v ≤ 127 := h
theorem lam_64 (v : UInt32) (h : v ≤ lam4 (by decide)) : v ≤ 127 := h
theorem lam_65 (v : UInt32) (h : v ≤ lam5 (by decide)) : v ≤ 127 := h

end RLI434S
