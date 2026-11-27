import Init

/- BET-1525: fixtures of the literal arithmetic case of the transport pass (tests/litarith_*.v, README, "Transport
   of proof arguments across Nat literals"). Each theorem passes a proof of `Q 65536 a` where `Q 65536 d` is
   expected, `a` and `d` closed terms of the same value whose conversion needs Nat arithmetic; `Q` is an axiom,
   so that the expected type holds the pair and the literal 65536 (the argument's gate). Most pairs are two
   constants `mk_x` and `mk_x'` at `α × Nat` whose second fields are `65536 - 31` and `65505`: a held
   subtraction whose sub-lemma gives the pair a proof to make. Every definition comes first in the export (its
   names list), then the theorems in one range of export lines per test file, so that a test imports the
   definitions and its own range only. -/
namespace RLI434L

axiom Q {α : Type} : Nat → α → Prop
axiom Q2 {α β : Type} : Nat → α → β → Prop
axiom axN : Nat
axiom axB : Bool
axiom axP : Nat × Nat
axiom axF : Nat → Nat

structure Tag (n : Nat) where
  val : Nat

structure Pk where
  n : Nat
  t : Tag n

-- the own entry of tests/litarith_absent.v and tests/litarith_nobool.v: the Mul row's certificate alone
def ca : Option Nat := some (4294967296 * 2)
def cb : Option Nat := some 8589934592

-- class 1: a match, a fixpoint and a projection on a constructor
def mk_cm : Nat × Nat := (cond true 1 0, 65536 - 31)
def mk_cm' : Nat × Nat := (1, 65505)
noncomputable def mk_cf : Nat × Nat := (Nat.rec (motive := fun _ => Nat) 1 (fun _ ih => ih) 2, 65536 - 31)
def mk_cf' : Nat × Nat := (1, 65505)
def mk_cp : Nat × Nat := ((1, 0).1, 65536 - 31)
def mk_cp' : Nat × Nat := (1, 65505)

-- class 2: a dependent eliminator waiting on a held operation, with no proof or fixed type holding it
noncomputable def wtd_a : Pk :=
  ⟨65536 + 1, Nat.casesOn (motive := fun _ => Tag (65536 + 1)) (65536 - 1) ⟨0⟩ (fun _ => ⟨1⟩)⟩
def wtd_d : Pk := ⟨65536 + 1, ⟨1⟩⟩
-- the same at Fin (65536 + 1): the pair's type and the values' `by decide` proofs hold the held operation
noncomputable def mpf_a : Fin (65536 + 1) :=
  Nat.casesOn (motive := fun _ => Fin (65536 + 1)) (65536 - 1) ⟨0, by decide⟩ (fun _ => ⟨1, by decide⟩)

def mk_wm : Nat × Nat := (cond (decide (256 ∣ 256 * 65536)) 1 0, 65536 - 31)
def mk_wm' : Nat × Nat := (1, 65505)
def mk_wu : Nat × Nat := (cond (decide (257 ∣ 256 * 65536)) 1 0, 65536 - 31)
def mk_wu' : Nat × Nat := (cond (decide (257 ∣ 256 * 65536)) 1 0, 65505)
def mk_em : Nat × Nat × Nat := let c := cond (decide (257 ∣ 256 * 65536)) 1 0; (c, c, 65536 - 31)
def mk_em' : Nat × Nat × Nat :=
  (cond (decide (257 ∣ 256 * 65536)) 1 0, cond (decide (257 ∣ 256 * 65536)) 1 0, 65505)

-- class 3: a match (on Bool), a fixpoint and a projection on an axiom; a head with no body; a lambda's body
noncomputable def mk_sm : Nat × Nat := (cond axB 1 2, 65536 - 31)
noncomputable def mk_sm' : Nat × Nat := (cond axB 1 2, 65505)
noncomputable def mk_sf : Nat × Nat := (Nat.rec (motive := fun _ => Nat) 1 (fun _ ih => ih) axN, 65536 - 31)
noncomputable def mk_sf' : Nat × Nat := (Nat.rec (motive := fun _ => Nat) 1 (fun _ ih => ih) axN, 65505)
noncomputable def mk_sp : Nat × Nat := (axP.1, 65536 - 31)
noncomputable def mk_sp' : Nat × Nat := (axP.1, 65505)
noncomputable def mk_sh : Nat × Nat := (axF 3, 65536 - 31)
noncomputable def mk_sh' : Nat × Nat := (axF 3, 65505)
noncomputable def mk_spa : (Unit → Nat) × Nat :=
  (fun _ => Nat.casesOn (motive := fun _ => Nat) axN 1 (fun _ => 2), 65536 - 31)
noncomputable def mk_spa' : (Unit → Nat) × Nat :=
  (fun _ => Nat.casesOn (motive := fun _ => Nat) axN 1 (fun _ => 2), 65505)
noncomputable def mk_fu : Nat × Nat := (axN + 3, 65536 - 31)
noncomputable def mk_fu' : Nat × Nat := (axN + 3, 65505)

-- normal forms that compare Unknown; nothing held; two values that differ; a pair at a function type
def mk_un : Option (Fin (1 + 1)) × Nat := (some ⟨0, by decide⟩, 65536 - 31)
def mk_un' : Option (Fin 2) × Nat := (some ⟨0, by decide⟩, 65505)
def on1 (n : Nat) : Option Nat := some n
def on2 (n : Nat) : Option Nat := some n
def ign (_ : Option Nat × Nat) : Nat := 0
def mk_d1 : Option Nat × Nat := (some 0, 65536 - 31)
def mk_d2 : Option Nat × Nat := (some 1, 65505)
def tf1 : Nat → Nat := fun x => x + (65536 - 31)
def tf2 : Nat → Nat := fun x => x + (65536 - 31)

-- max_rounds: one round per level of gr, each waiting on a new held x - 65536
noncomputable def gr : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => Nat.casesOn (motive := fun _ => Nat) (x - 65536) (gr k (x + 1)) (fun _ => gr k (x + 1))

-- held operations: the threshold of each function, a held operand, an operand of no value or no reader
def mk_hs1 : Nat × Nat := (65535 - 65534, 65536 - 31)
def mk_hs2 : Nat × Nat := (65536 - 65535, 65536 - 31)
def mk_hs3 : Nat × Nat := (65537 - 65536, 65536 - 31)
def mk_hd1 : Nat × Nat := (65535 / 2, 65536 - 31)
def mk_hd2 : Nat × Nat := (65536 / 2, 65536 - 31)
def mk_hd3 : Nat × Nat := (65537 / 2, 65536 - 31)
def mk_hmo : Nat × Nat := (65536 * 1, 65536 - 31)
def mk_ha1 : Nat × Nat := (32768 + 32767, 65536 - 31)
def mk_ha2 : Nat × Nat := (32768 + 32768, 65536 - 31)
def mk_ha3 : Nat × Nat := (32768 + 32769, 65536 - 31)
def mk_hx1 : Nat × Nat := (255 * 257, 65536 - 31)
def mk_hx2 : Nat × Nat := (256 * 256, 65536 - 31)
def mk_hw : Nat × Nat := (2 ^ 16, 65536 - 31)
def mk_ho : Nat × Nat := ((4294967296 - (4294967296 - 5)) - 2, 65536 - 31)
def mk_ho' : Nat × Nat := (3, 65505)
noncomputable def mk_hu : Nat × Nat := (axF 3 + 3, 65536 - 31)
noncomputable def mk_hu' : Nat × Nat := (axF 3 + 3, 65505)

-- a % below and at the threshold, and in a constructor's parameter (Lean's function, the class function)
def mk_hm1 : Nat × Nat := (65535 % 7, 65536 - 31)
def mk_hm1' : Nat × Nat := (1, 65505)
def mk_hm2 : Nat × Nat := (65536 % 7, 65536 - 31)
def mk_hm2' : Nat × Nat := (2, 65505)
def mk_hf : Tag (Nat.mod 65536 7) × Nat := (⟨0⟩, 65536 - 31)
def mk_hf' : Tag (Nat.mod 65536 7) × Nat := (⟨0⟩, 65505)
def mk_hc : Tag (65536 % 7) × Nat := (⟨0⟩, 65536 - 31)
def mk_hc' : Tag (65536 % 7) × Nat := (⟨0⟩, 65505)

-- Nat.beq and Nat.ble: two literals below 65536, an operand of 65536 or more, a held operand
def mk_bst : Nat := cond (Nat.beq 65535 65535) (65536 - 31) (65536 - 30)
def mk_bsf : Nat := cond (Nat.beq 65535 3) (65536 - 31) (65536 - 30)
def mk_bls : Nat := cond (Nat.ble 65535 3) (65536 - 31) (65536 - 30)
def mk_bbg : Nat := cond (Nat.beq 65536 3) (65536 - 31) (65536 - 30)
def mk_bb1 : Nat := cond (Nat.beq 65537 3) (65536 - 31) (65536 - 30)
def mk_blb : Nat := cond (Nat.ble 3 65536) (65536 - 31) (65536 - 30)
def mk_bhd : Nat := cond (Nat.beq (65536 - 1) 3) (65536 - 31) (65536 - 30)

-- Lean's truncated subtraction; a division by 0 beside a second place
def mk_zs : Nat × Nat := ((65536 - (65536 - 5)) - 7, 65536 - 31)
def mk_zs' : Nat × Nat := (0, 65505)
def mk_tp : Nat × Nat := (1, 65536 - 31)
def mk_tp' : Nat × Nat := (1, 65505)

-- max_bits: L's held arm at 1023 and 1024 bits, and powers of 1024 and 1025 bits written on both sides
def mk_bk3 : Nat × Nat :=
  (6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048 *
    6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048,
   65536 - 31)
def mk_bk4 : Nat × Nat :=
  (13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 *
    6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048,
   65536 - 31)
def mk_pw : Nat × Nat := (2 ^ 1023, 65536 - 31)
def mk_pw' : Nat × Nat := (2 ^ 1023, 65505)
def mk_pv : Nat × Nat := (2 ^ 1024, 65536 - 31)
def mk_pv' : Nat × Nat := (2 ^ 1024, 65505)

-- decide and prove_prop: a divisor 0, a decide whose only large term is a held subtraction, Nat_le, eq at Nat
-- and at a data type, Int.NonNeg of Int.ofNat and of Int.negSucc
def mk_zd : Nat × Nat := (cond (decide (0 ∣ 65536)) 1 0, 65536 - 31)
def mk_zd' : Nat × Nat := (cond (decide (0 ∣ 65536)) 1 0, 65505)
def mk_zd2 : Nat × Nat := (cond (decide (0 ∣ 65536 - 65536)) 1 0, 65536 - 31)
def mk_zd2' : Nat × Nat := (cond (decide (0 ∣ 65536 - 65536)) 1 0, 65505)
def mk_pl : Nat × Nat := (cond (decide (65536 ≤ 65536 + 1)) 1 0, 65536 - 31)
def mk_pl' : Nat × Nat := (1, 65505)
def mk_pe : Nat × Nat := (cond (decide (65536 ≤ 65536)) 1 0, 65536 - 31)
def mk_pe' : Nat × Nat := (1, 65505)
def mk_en : Nat × Nat := (cond (decide (65536 * 2 = 2 * 65536)) 1 0, 65536 - 31)
def mk_en' : Nat × Nat := (1, 65505)
def mk_ed : Nat × Nat := (cond (decide ((65536 - 1, 1) = (65535, 1))) 1 0, 65536 - 31)
def mk_ed' : Nat × Nat := (1, 65505)
def mk_pn : Nat × Nat := (cond (decide ((0 : Int) ≤ Int.ofNat 65536)) 1 0, 65536 - 31)
def mk_pn' : Nat × Nat := (1, 65505)
def mk_nn : Nat × Nat := (cond (decide ((0 : Int) ≤ Int.negSucc 65536)) 1 0, 65536 - 31)
def mk_nn' : Nat × Nat := (cond (decide ((0 : Int) ≤ Int.negSucc 65536)) 1 0, 65505)

-- M12's fallback head reduction: 63, 64 and 65 steps from 0 to `65536 = 65536`, two a level and one for a let
def kp0 (x : Nat) : Prop := x = x
def kp1 (x : Nat) : Prop := kp0 x
def kp2 (x : Nat) : Prop := kp1 x
def kp3 (x : Nat) : Prop := kp2 x
def kp4 (x : Nat) : Prop := kp3 x
def kp5 (x : Nat) : Prop := kp4 x
def kp6 (x : Nat) : Prop := kp5 x
def kp7 (x : Nat) : Prop := kp6 x
def kp8 (x : Nat) : Prop := kp7 x
def kp9 (x : Nat) : Prop := kp8 x
def kp10 (x : Nat) : Prop := kp9 x
def kp11 (x : Nat) : Prop := kp10 x
def kp12 (x : Nat) : Prop := kp11 x
def kp13 (x : Nat) : Prop := kp12 x
def kp14 (x : Nat) : Prop := kp13 x
def kp15 (x : Nat) : Prop := kp14 x
def kp16 (x : Nat) : Prop := kp15 x
def kp17 (x : Nat) : Prop := kp16 x
def kp18 (x : Nat) : Prop := kp17 x
def kp19 (x : Nat) : Prop := kp18 x
def kp20 (x : Nat) : Prop := kp19 x
def kp21 (x : Nat) : Prop := kp20 x
def kp22 (x : Nat) : Prop := kp21 x
def kp23 (x : Nat) : Prop := kp22 x
def kp24 (x : Nat) : Prop := kp23 x
def kp25 (x : Nat) : Prop := kp24 x
def kp26 (x : Nat) : Prop := kp25 x
def kp27 (x : Nat) : Prop := kp26 x
def kp28 (x : Nat) : Prop := kp27 x
def kp29 (x : Nat) : Prop := kp28 x
def kp30 (x : Nat) : Prop := kp29 x
def kp31 (x : Nat) : Prop := kp30 x
def mk_fb63 : Nat × Nat :=
  (cond (@decide (let y := 65536; kp30 y) (inferInstanceAs (Decidable (65536 = 65536)))) 1 0, 65536 - 31)
def mk_fb64 : Nat × Nat := (cond (@decide (kp31 65536) (inferInstanceAs (Decidable (65536 = 65536)))) 1 0, 65536 - 31)
def mk_fb65 : Nat × Nat :=
  (cond (@decide (let y := 65536; kp31 y) (inferInstanceAs (Decidable (65536 = 65536)))) 1 0, 65536 - 31)
def mk_fb' : Nat × Nat := (1, 65505)

-- nested evaluations: a stuck eliminator inside the nested pair, with and without the outer match waiting
noncomputable def hN (n : Nat) : Option Nat := Nat.casesOn (motive := fun _ => Option Nat) n (some 0) (fun _ => none)
noncomputable def mk_ns : Bool × Nat := (decide ((hN axN, 65536) = (hN axN, 65536)), 65536 - 31)
noncomputable def mk_ns' : Bool × Nat := (decide ((hN axN, 65536) = (hN axN, 65536)), 65505)
noncomputable def mk_nw : Nat × Nat := (cond (decide ((hN axN, 65536) = (hN axN, 65536))) 1 0, 65536 - 31)
noncomputable def mk_nw' : Nat × Nat := (cond (decide ((hN axN, 65536) = (hN axN, 65536))) 1 0, 65505)

-- the refusals (tests/litarith_refused.v, on litarith_planted.ndjson, where pmod is the planted Nat.mod, of the
-- value of zmod, and ppred the planted Nat.pred, of the value of idn; here both are Lean's functions; zmod and
-- idn come first, so that their values are in the export before pmod and ppred)
def zmod (_x _y : Nat) : Nat := 0
def pmod (x y : Nat) : Nat := x % y
def idn (n : Nat) : Nat := n
def ppred (n : Nat) : Nat := n.pred
def mk_k1 : Nat × Nat := (pmod 7 3, 65536 + 31)
def mk_k2 : Nat × Nat := (pmod 8 3, 65536 + 31)
def kd1 : Nat × Nat := (1, 65567)
def mk_s1 : Nat × Nat := (0, 65536 - 31)

-- the absent names (tests/litarith_absent.v): the replacement field 65536 + 31, the Add row's certificate
def mk_hma : Nat × Nat := (65536 % 7, 65536 + 31)
def mk_hma' : Nat × Nat := (2, 65567)
def mk_bsa : Nat := cond (Nat.beq 65535 65535) (65536 + 31) (65536 + 30)
def mk_pna : Nat × Nat := (cond (decide ((0 : Int) ≤ Int.ofNat 65536)) 1 0, 65536 + 31)
def mk_pla : Nat × Nat := (cond (decide (65536 ≤ 65536 + 1)) 1 0, 65536 + 31)
def mk_a' : Nat × Nat := (1, 65567)

theorem own_mul (h : Q 65536 ca) : Q 65536 cb := h

-- tests/litarith_eval.v
theorem tidy_big (h : Q 65536 (Lean.Omega.tidyConstraint ⟨some 4294967296, none⟩ ([4096] : List Int))) :
    Q 65536 (⟨some 1048576, none⟩ : Lean.Omega.Constraint) := h
theorem c_match (h : Q 65536 mk_cm) : Q 65536 mk_cm' := h
theorem c_fix (h : Q 65536 mk_cf) : Q 65536 mk_cf' := h
theorem c_proj (h : Q 65536 mk_cp) : Q 65536 mk_cp' := h
theorem w_fix (h : Q 65536 (Int.subNatNat 65536 32)) : Q 65536 (Int.ofNat 65504) := h
theorem w_fix_dep (h : Q 65536 wtd_a) : Q 65536 wtd_d := h
theorem motive_proof (h : Q 65536 mpf_a) : Q 65536 (⟨1, by decide⟩ : Fin (65536 + 1)) := h
theorem w_match (h : Q 65536 mk_wm) : Q 65536 mk_wm' := h
theorem w_unresolved (h : Q 65536 mk_wu) : Q 65536 mk_wu' := h
theorem e_memo (h : Q 65536 mk_em) : Q 65536 mk_em' := h
theorem s_match (h : Q 65536 mk_sm) : Q 65536 mk_sm' := h
theorem s_fix (h : Q 65536 mk_sf) : Q 65536 mk_sf' := h
theorem s_proj (h : Q 65536 mk_sp) : Q 65536 mk_sp' := h
theorem s_head (h : Q 65536 mk_sh) : Q 65536 mk_sh' := h
theorem s_param (h : Q 65536 mk_spa) : Q 65536 mk_spa' := h
theorem field_unvalued (h : Q 65536 mk_fu) : Q 65536 mk_fu' := h
theorem nothing_held (h : Q 65536 (on1 3)) : Q 65536 (on2 3) := h
theorem unknown_param (h : Q 65536 mk_un) : Q 65536 mk_un' := h
theorem values_differ_l (h : Q2 65536 (ign mk_d1) (4999 + 1)) : Q2 65536 (ign mk_d2) 5000 := h
theorem same_heads (h : Q 65536 (some (65536 - 31))) : Q 65536 (some 65505) := h
theorem open_pair_l (h : ∀ x : Nat, Q 65536 (x + (65536 - 31))) : ∀ x : Nat, Q 65536 (x + 65505) := h
theorem type_fun (h : Q 65536 tf1) : Q 65536 tf2 := h
theorem rounds_15 (h : Q 65536 (gr 15 65536, 65536 - 31)) : Q 65536 (65536 + 15, 65505) := h
theorem rounds_16 (h : Q 65536 (gr 16 65536, 65536 - 31)) : Q 65536 (65536 + 16, 65505) := h
theorem rounds_17 (h : Q 65536 (gr 17 65536, 65536 - 31)) : Q 65536 (65536 + 17, 65505) := h

-- tests/litarith_hold.v
theorem div_held_l (h : Q 65536 (4294967296 / 64)) : Q 65536 67108864 := h
theorem hmin_sub_op_65535 (h : Q 65536 mk_hs1) : Q 65536 ((1 : Nat), (65505 : Nat)) := h
theorem hmin_sub_op_65536 (h : Q 65536 mk_hs2) : Q 65536 ((1 : Nat), (65505 : Nat)) := h
theorem hmin_sub_op_65537 (h : Q 65536 mk_hs3) : Q 65536 ((1 : Nat), (65505 : Nat)) := h
theorem hmin_div_op_65535 (h : Q 65536 mk_hd1) : Q 65536 ((32767 : Nat), (65505 : Nat)) := h
theorem hmin_div_op_65536 (h : Q 65536 mk_hd2) : Q 65536 ((32768 : Nat), (65505 : Nat)) := h
theorem hmin_div_op_65537 (h : Q 65536 mk_hd3) : Q 65536 ((32768 : Nat), (65505 : Nat)) := h
theorem hmin_mul_op_65536 (h : Q 65536 mk_hmo) : Q 65536 ((65536 : Nat), (65505 : Nat)) := h
theorem hmin_add_val_65535 (h : Q 65536 mk_ha1) : Q 65536 ((65535 : Nat), (65505 : Nat)) := h
theorem hmin_add_val_65536 (h : Q 65536 mk_ha2) : Q 65536 ((65536 : Nat), (65505 : Nat)) := h
theorem hmin_add_val_65537 (h : Q 65536 mk_ha3) : Q 65536 ((65537 : Nat), (65505 : Nat)) := h
theorem hmin_mul_val_65535 (h : Q 65536 mk_hx1) : Q 65536 ((65535 : Nat), (65505 : Nat)) := h
theorem hmin_mul_val_65536 (h : Q 65536 mk_hx2) : Q 65536 ((65536 : Nat), (65505 : Nat)) := h
theorem hmin_pow_val_65536 (h : Q 65536 mk_hw) : Q 65536 ((65536 : Nat), (65505 : Nat)) := h
theorem h_operand (h : Q 65536 mk_ho) : Q 65536 mk_ho' := h
theorem unvalued_head (h : Q 65536 mk_hu) : Q 65536 mk_hu' := h
theorem lit_4999 (h : Q 65536 (65536 - 60537)) : Q 65536 4999 := h
theorem lit_5000 (h : Q 65536 (65536 - 60536)) : Q 65536 5000 := h
theorem lit_5001 (h : Q 65536 (65536 - 60535)) : Q 65536 5001 := h
theorem mod_65535 (h : Q 65536 mk_hm1) : Q 65536 mk_hm1' := h
theorem mod_65536 (h : Q 65536 mk_hm2) : Q 65536 mk_hm2' := h
theorem mod_in_form (h : Q 65536 mk_hf) : Q 65536 mk_hf' := h
theorem mod_in_form_cls (h : Q 65536 mk_hc) : Q 65536 mk_hc' := h
theorem beq_small_t (h : Q 65536 mk_bst) : Q 65536 65505 := h
theorem beq_small_f (h : Q 65536 mk_bsf) : Q 65536 65506 := h
theorem ble_small (h : Q 65536 mk_bls) : Q 65536 65506 := h
theorem beq_big (h : Q 65536 mk_bbg) : Q 65536 65506 := h
theorem beq_big1 (h : Q 65536 mk_bb1) : Q 65536 65506 := h
theorem ble_big (h : Q 65536 mk_blb) : Q 65536 65505 := h
theorem beq_held (h : Q 65536 mk_bhd) : Q 65536 65506 := h
theorem sub_held (h : Q 65536 (65536 - 31)) : Q 65536 65505 := h
theorem sub_held_l (h : Q 65536 (4294967296 - 16)) : Q 65536 4294967280 := h
theorem sub_trunc (h : Q 65536 mk_zs) : Q 65536 mk_zs' := h
theorem div_held (h : Q 65536 (65536 / 64)) : Q 65536 1024 := h
theorem two_pairs_subfail (h : Q2 65536 (65536 / 0) mk_tp) : Q2 65536 0 mk_tp' := h
theorem z_ord (h : Q2 65536 (5000 + 65536 / 0) (2 ^ 32)) : Q2 65536 5000 4294967296 := h
theorem bits_1025 (h : Q 65536
    (13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 *
      13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096,
     65536 - 31)) :
    Q 65536 ((179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 : Nat), (65505 : Nat)) := h
theorem pow_1025b (h : Q 65536 mk_pv) : Q 65536 mk_pv' := h
theorem bits_1023 (h : Q 65536
    (6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048 *
      6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048,
     65536 - 31)) :
    Q 65536 ((44942328371557897693232629769725618340449424473557664318357520289433168951375240783177119330601884005280028469967848339414697442203604155623211857659868531094441973356216371319075554900311523529863270738021251442209537670585615720368478277635206809290837627671146574559986811484619929076208839082406056034304 : Nat), (65505 : Nat)) := h
theorem bits_1024 (h : Q 65536
    (13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 *
      6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048,
     65536 - 31)) :
    Q 65536 ((89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608 : Nat), (65505 : Nat)) := h
theorem lbits_1023 (h : Q 65536 mk_bk3) :
    Q 65536 ((44942328371557897693232629769725618340449424473557664318357520289433168951375240783177119330601884005280028469967848339414697442203604155623211857659868531094441973356216371319075554900311523529863270738021251442209537670585615720368478277635206809290837627671146574559986811484619929076208839082406056034304 : Nat), (65505 : Nat)) := h
theorem lbits_1024 (h : Q 65536 mk_bk4) :
    Q 65536 ((89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608 : Nat), (65505 : Nat)) := h
theorem pow_1024b (h : Q 65536 mk_pw) : Q 65536 mk_pw' := h

-- tests/litarith_dvd.v
theorem dvd_256 (h : Q 65536 (decide (256 ∣ 4294967296))) : Q 65536 true := h
theorem dvd_zero (h : Q 65536 mk_zd) : Q 65536 mk_zd' := h
theorem dvd_zero_sub (h : Q 65536 mk_zd2) : Q 65536 mk_zd2' := h
theorem le_big (h : Q 65536 mk_pl) : Q 65536 mk_pl' := h
theorem le_eq (h : Q 65536 mk_pe) : Q 65536 mk_pe' := h
theorem eq_nat (h : Q 65536 mk_en) : Q 65536 mk_en' := h
theorem eq_data (h : Q 65536 mk_ed) : Q 65536 mk_ed' := h
theorem nonneg (h : Q 65536 mk_pn) : Q 65536 mk_pn' := h
theorem nonneg_neg (h : Q 65536 mk_nn) : Q 65536 mk_nn' := h
theorem fb12_63 (h : Q 65536 mk_fb63) : Q 65536 mk_fb' := h
theorem fb12_64 (h : Q 65536 mk_fb64) : Q 65536 mk_fb' := h
theorem fb12_65 (h : Q 65536 mk_fb65) : Q 65536 mk_fb' := h
theorem nested_stop (h : Q 65536 mk_ns) : Q 65536 mk_ns' := h
theorem nested_wait (h : Q 65536 mk_nw) : Q 65536 mk_nw' := h

-- tests/litarith_refused.v (on litarith_planted.ndjson)
theorem refused_hole (h : Q2 65536 mk_k1 mk_k2) : Q2 65536 ((1 : Nat), (65567 : Nat)) ((2 : Nat), (65567 : Nat)) := h
theorem refused_sub (h : Q2 65536 mk_s1 (4999 + 1)) : Q2 65536 ((0 : Nat), (65505 : Nat)) (5000 : Nat) := h
theorem refused_twice (h : Q 65536 mk_k1) : Q 65536 kd1 ∧ Q 65536 kd1 := ⟨h, h⟩
theorem refused_again (h : Q 65536 mk_k1) : Q 65536 kd1 := h

-- tests/litarith_absent.v (on litarith_absent.ndjson)
theorem sub_held_a (h : Q 65536 (65536 - 31)) : Q 65536 65505 := h
theorem div_held_a (h : Q 65536 (65536 / 64)) : Q 65536 1024 := h
theorem mod_65536_a (h : Q 65536 mk_hma) : Q 65536 mk_hma' := h
theorem beq_small_a (h : Q 65536 mk_bsa) : Q 65536 65567 := h
theorem nonneg_a (h : Q 65536 mk_pna) : Q 65536 mk_a' := h
theorem le_big_a (h : Q 65536 mk_pla) : Q 65536 mk_a' := h

-- tests/litarith_budget.v: the budget runs, each with terms of its own
theorem bud_tidy (h : Q 65536 (Lean.Omega.tidyConstraint ⟨some 8589934592, none⟩ ([8192] : List Int))) :
    Q 65536 (⟨some 1048576, none⟩ : Lean.Omega.Constraint) := h

def mk_bh : Nat × Nat := ((4294967296 - (4294967296 - 7)) - 4, 65536 - 32)
def mk_bh' : Nat × Nat := (3, 65504)
theorem bud_dvd (h : Q 65536 (decide (512 ∣ 8589934592))) : Q 65536 true := h
theorem bud_hold (h : Q 65536 mk_bh) : Q 65536 mk_bh' := h

-- thirty-three arguments, each a pair of its own (a held decide, the cost of dvd_256's) beside an entry part that is
-- smaller than one argument's: the parts together pass 10 times the largest (the entry's own statement is scanned once
-- per argument, so its largest part grows with the arguments' number: 12 of them left it above a tenth of the total)
theorem bud_total (h0 : Q 65536 (decide (2 ∣ 8589934592))) (h1 : Q 65536 (decide (4 ∣ 8589934592))) (h2 : Q 65536 (decide (8 ∣ 8589934592))) (h3 : Q 65536 (decide (16 ∣ 8589934592))) (h4 : Q 65536 (decide (32 ∣ 8589934592))) (h5 : Q 65536 (decide (64 ∣ 8589934592))) (h6 : Q 65536 (decide (128 ∣ 8589934592))) (h7 : Q 65536 (decide (256 ∣ 8589934592))) (h8 : Q 65536 (decide (512 ∣ 8589934592))) (h9 : Q 65536 (decide (1024 ∣ 8589934592))) (h10 : Q 65536 (decide (2048 ∣ 8589934592))) (h11 : Q 65536 (decide (4096 ∣ 8589934592))) (h12 : Q 65536 (decide (8192 ∣ 8589934592))) (h13 : Q 65536 (decide (16384 ∣ 8589934592))) (h14 : Q 65536 (decide (32768 ∣ 8589934592))) (h15 : Q 65536 (decide (65536 ∣ 8589934592))) (h16 : Q 65536 (decide (131072 ∣ 8589934592))) (h17 : Q 65536 (decide (262144 ∣ 8589934592))) (h18 : Q 65536 (decide (524288 ∣ 8589934592))) (h19 : Q 65536 (decide (1048576 ∣ 8589934592))) (h20 : Q 65536 (decide (2097152 ∣ 8589934592))) (h21 : Q 65536 (decide (4194304 ∣ 8589934592))) (h22 : Q 65536 (decide (8388608 ∣ 8589934592))) (h23 : Q 65536 (decide (16777216 ∣ 8589934592))) (h24 : Q 65536 (decide (33554432 ∣ 8589934592))) (h25 : Q 65536 (decide (67108864 ∣ 8589934592))) (h26 : Q 65536 (decide (134217728 ∣ 8589934592))) (h27 : Q 65536 (decide (268435456 ∣ 8589934592))) (h28 : Q 65536 (decide (536870912 ∣ 8589934592))) (h29 : Q 65536 (decide (1073741824 ∣ 8589934592))) (h30 : Q 65536 (decide (2147483648 ∣ 8589934592))) (h31 : Q 65536 (decide (4294967296 ∣ 8589934592))) (h32 : Q 65536 (decide (8589934592 ∣ 8589934592))) :
    Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true ∧ Q 65536 true :=
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩

-- a fixpoint that does not end within the cap
def lp1 : Nat × Nat := (Nat.repeat id 4294967296 0, 65536 - 31)
def lp2 : Nat × Nat := (Nat.repeat id 4294967296 0, 65536 - 31)
theorem loop_head (h : Q 65536 lp1) : Q 65536 lp2 := h

-- tests/litarith_budget.v: the helpers of litarith_deep.ndjson's chains (the pair's cap, its leaf in ida and idb)
-- and its nesting (D-depth, dwrap over mk_dp)
def ida (x : Nat) : Nat := x
def idb (x _y : Nat) : Nat := x
def dwrap (x : Nat × Nat) : Nat × Nat := x
def mk_dp : Nat × Nat := (cond true 1 0, 65536 - 31)
def mk_dp' : Nat × Nat := (1, 65505)

set_option maxRecDepth 100000

-- the cap reached inside a nested evaluation: ncA needs more than 200000 charges
def ncA : Nat := (List.replicate 100 0).length
def mk_nc : Bool × Nat := (decide ((ncA, 65536) = (100, 65536)), 65536 - 31)
def mk_nc' : Bool × Nat := (decide ((ncA, 65536) = (100, 65536)), 65505)
theorem nested_cap (h : Q 65536 mk_nc) : Q 65536 mk_nc' := h

-- one charge that takes the part and the pair below zero, or the total and the pair: a pair of more than
-- 200000 charges in the entry's own result
def capA_big : Nat × Nat := ((List.replicate 100 0).length, 65536 - 31)
def capD_big : Nat × Nat := (100, 65505)
theorem order_pair (h : Q 65536 capA_big) : Q 65536 capD_big := h
axiom keep9 : Q 65536 capD_big → Q 65536 capD_big → Q 65536 capD_big → Q 65536 capD_big → Q 65536 capD_big →
  Q 65536 capD_big → Q 65536 capD_big → Q 65536 capD_big → Q 65536 capD_big → Q 65536 capA_big → Q 65536 capA_big
theorem order_total (h : Q 65536 capA_big) (_b : (1000 : Nat) = 1000) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_b (h : Q 65536 capA_big) (_b : (1001 : Nat) = 1001) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_c (h : Q 65536 capA_big) (_b : (1002 : Nat) = 1002) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_d (h : Q 65536 capA_big) (_b : (1003 : Nat) = 1003) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_e (h : Q 65536 capA_big) (_b : (1004 : Nat) = 1004) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_f (h : Q 65536 capA_big) (_b : (1005 : Nat) = 1005) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_g (h : Q 65536 capA_big) (_b : (1006 : Nat) = 1006) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_h (h : Q 65536 capA_big) (_b : (1007 : Nat) = 1007) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_i (h : Q 65536 capA_big) (_b : (1008 : Nat) = 1008) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h
theorem order_total_j (h : Q 65536 capA_big) (_b : (1009 : Nat) = 1009) : Q 65536 capD_big :=
  keep9 h h h h h h h h h h

-- exponential sharing: dupT applied 60 times, each application's argument shared by the two sons of the next
-- (2 ^ 60 nodes as a tree, 61 as a graph): the pair gets no lemma at the pair's cap, and the kernel converts the
-- two sides, whose first fields are the same term, by their second fields
inductive Tr : Type
  | leaf (n : Nat) : Tr
  | node (l r : Tr) : Tr
def dupT (x : Tr) : Tr := Tr.node x x
def expo_a : Tr × Nat := (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (Tr.leaf 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), 65536 - 31)
def expo_d : Tr × Nat := (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (dupT (Tr.leaf 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), 65505)
theorem expo_share (h : Q 65536 expo_a) : Q 65536 expo_d := h

-- row E-cap's knobs, applied to the top of a chain of litarith_deep.ndjson (a list of constants): each application
-- adds a few steps to the pair's evaluation
def idl (x : List Nat) : List Nat := x
def idl2 (x : List Nat) (_y : Nat) : List Nat := x
def idl3 (x : List Nat) (_y _z : Nat) : List Nat := x

-- the row mutants' fixtures, after every earlier line of the export (so no earlier line moves), one range of export
-- lines per test file. T-query: a pair at a function type whose evaluation holds a decide at an evaluated position
-- (le_big's), so that only the bounded query of the type's sort leaves it without a hole (tests/litarith_eval.v)
def tfa : Nat → Nat := cond (decide (65536 ≤ 65536 + 1)) (fun x => x) (fun x => x + 1)
def tfd : Nat → Nat := fun x => x
theorem type_fun_held (h : Q 65536 tfa) : Q 65536 tfd := h
-- P-eq-nat and P-nonneg at 2 ^ 33, whose two sides the kernel cannot compute within the entry's limit, so that a
-- proof of the wrong direction is not converted (tests/litarith_dvd.v)
def mk_enl : Nat × Nat := (cond (decide (4294967296 * 2 = 2 * 4294967296)) 1 0, 65536 - 31)
def mk_enl' : Nat × Nat := (1, 65505)
theorem eq_nat_l (h : Q 65536 mk_enl) : Q 65536 mk_enl' := h
def mk_pnl : Nat × Nat := (cond (decide ((0 : Int) ≤ Int.ofNat (4294967296 * 2))) 1 0, 65536 - 31)
def mk_pnl' : Nat × Nat := (1, 65505)
theorem nonneg_l (h : Q 65536 mk_pnl) : Q 65536 mk_pnl' := h
-- M7-div in the direct form Nat.div, which the bridge casts from the theorem's HDiv.hDiv (tests/litarith_hold.v)
theorem div_held_d (h : Q 65536 (Nat.div 4294967296 64)) : Q 65536 67108864 := h
-- K-repeat: the refused pair of refused_twice in two arguments whose types are the same terms, the domain of both
-- arguments being both's one implicit argument (tests/litarith_refused.v)
theorem both {p : Prop} (a : p) (_b : p) : p := a
theorem refused_shared (h : Q 65536 mk_k1) : Q 65536 kd1 := @both (Q 65536 kd1) h h
-- C-match through Bool's first constructor: cond false, whose branch is the first of two, so that the row's mutant
-- (the branch index off by one) takes the other branch and the values differ (tests/litarith_eval.v)
def mk_cmf : Nat × Nat := (cond false 0 1, 65536 - 31)
theorem c_match_f (h : Q 65536 mk_cmf) : Q 65536 mk_cm' := h
-- held_rep: two held additions of one key and one form whose first operands differ as terms, 2 ^ 32 and the
-- literal 4294967296: each is its own representative, so that the kernel never converts the literal with 2 ^ 32
-- (tests/litarith_hold.v)
def mk2 (x y : Nat) : Nat × Nat := (x + 1, y + 1)
theorem held_rep_ops (h : Q 65536 (mk2 (2 ^ 32) 4294967296)) : Q 65536 ((2 ^ 32 + 1, 4294967296 + 1) : Nat × Nat) := h
-- held_ops: a held subtraction at an evaluated position beside a direct Nat.pow 2 8 (below 65536) in a parameter and
-- a proof (a Fin's bound and its decide proof), and a Nat place of the same argument (tests/litarith_hold.v)
def mk_fp : Fin (Nat.pow 2 8) × Nat := (⟨5, by decide⟩, 65536 - 31)
def mk_fp' : Fin (Nat.pow 2 8) × Nat := (⟨5, by decide⟩, 65505)
theorem held_small_param (h : Q2 65536 mk_fp (2 ^ 32)) : Q2 65536 mk_fp' 4294967296 := h
-- ec_proof: the final normal form holds sixteen copies of the literal 4999 (about 10000 nodes each as a tree), which
-- the last round puts in the place of a held 70535 - 65536 that dupT shares; the pair's walks stay far below the cap,
-- the proof's tree does not (tests/litarith_budget.v)
def mk_ps : Tr × Nat := (dupT (dupT (dupT (dupT (Tr.leaf (70535 - 65536))))), 65536 - 31)
def mk_ps' : Tr × Nat := (dupT (dupT (dupT (dupT (Tr.leaf (70535 - 65536))))), 65505)
theorem proof_size (h : Q 65536 mk_ps) : Q 65536 mk_ps' := h
-- nat_diff: a nest of six pairs, each declined at the cap (ncA's evaluation alone needs more than it), beside a Nat
-- place of the same argument (tests/litarith_budget.v)
def nf1 (x : Nat) : Nat := x
def nf2 (x : Nat) : Nat := x
def nf3 (x : Nat) : Nat := x
def nf4 (x : Nat) : Nat := x
def nf5 (x : Nat) : Nat := x
def ng1 (x : Nat) : Nat := x
def ng2 (x : Nat) : Nat := x
def ng3 (x : Nat) : Nat := x
def ng4 (x : Nat) : Nat := x
def ng5 (x : Nat) : Nat := x
theorem nest_capped (h : Q2 65536 (nf1 (nf2 (nf3 (nf4 (nf5 ncA))))) (2 ^ 32)) :
    Q2 65536 (ng1 (ng2 (ng3 (ng4 (ng5 100))))) 4294967296 := h

-- A chain of waits (l-table-r8-A): a match, fixpoint or projection whose scrutinee, recursive argument or subject
-- is a match, fixpoint or projection that waits on a held operation (tests/litarith_eval.v, tests/litarith_dvd.v,
-- tests/litarith_budget.v)
noncomputable def isz (n : Nat) : Bool := Nat.casesOn (motive := fun _ => Bool) n true (fun _ => false)
noncomputable def pb (n : Nat) : Bool × Nat := Nat.casesOn (motive := fun _ => Bool × Nat) n (false, 0) (fun _ => (true, 0))
noncomputable def cz (n : Nat) : Nat := Nat.casesOn (motive := fun _ => Nat) n 0 (fun _ => 1)
noncomputable def ch_one : Nat × Nat := (1, 65505)
noncomputable def ch_cc : Nat × Nat := (cond (cond (decide (256 ∣ 256 * 65536)) true false) 1 0, 65536 - 31)
noncomputable def ch_cf : Nat × Nat := (cond (isz (65536 - 1)) 0 1, 65536 - 31)
noncomputable def ch_cp : Nat × Nat := (cond (pb (65536 - 1)).1 1 0, 65536 - 31)
noncomputable def ch_g0 : Nat × Nat :=
  (Option.casesOn (motive := fun _ => Nat)
    (Nat.casesOn (motive := fun _ => Option (Tag 65535)) (65536 - 1) none (fun _ => some ⟨0⟩)) 0 (fun _ => 1),
   65536 - 31)
noncomputable def ch_g1 : Nat × Nat :=
  (Option.casesOn (motive := fun _ => Nat)
    (Nat.casesOn (motive := fun _ => Option (Tag 65536)) (65536 - 1) none (fun _ => some ⟨0⟩)) 0 (fun _ => 1),
   65536 - 31)
noncomputable def ch_g2 : Nat × Nat :=
  (Option.casesOn (motive := fun _ => Nat)
    (Nat.casesOn (motive := fun _ => Option (Tag 65537)) (65536 - 1) none (fun _ => some ⟨0⟩)) 0 (fun _ => 1),
   65536 - 31)
noncomputable def ch_gf : Option (Tag 65536) × Nat :=
  (Nat.casesOn (motive := fun _ => Option (Tag 65536)) (cz (65536 - 1)) none (fun _ => some ⟨0⟩), 65536 - 31)
noncomputable def ch_gf' : Option (Tag 65536) × Nat := (some ⟨0⟩, 65505)
noncomputable def ch_ax : Nat × Nat := (cond (isz axN) 0 1, 65536 - 31)
noncomputable def ch_ax' : Nat × Nat := (cond (isz axN) 0 1, 65505)
noncomputable def ch_ns : Nat × Nat := (cond (decide ((0 : Int) ≤ Int.ofNat 65536 - 1)) 1 0, 65536 - 31)
noncomputable def ch_ks : Nat × Nat := (if (0 : Int) ≤ 256 * 256 - 1 then 1 else 0, 65536 - 31)
theorem chain_case (h : Q 65536 ch_cc) : Q 65536 ch_one := h
theorem chain_fix (h : Q 65536 ch_cf) : Q 65536 ch_one := h
theorem chain_proj (h : Q 65536 ch_cp) : Q 65536 ch_one := h
theorem chain_1 (h : Q 65536 (-(4096 * 117349959766017) + 1 : Int)) : Q 65536 (-480665435201605631 : Int) := h
theorem chain_2 (h : Q 65536 (-(4096 * 117349959766017) + 1 + 1 : Int)) : Q 65536 (-480665435201605630 : Int) := h
theorem chain_8 (h : Q 65536 (-(4096 * 117349959766017) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : Int)) :
    Q 65536 (-480665435201605624 : Int) := h
theorem chain_9 (h : Q 65536 (-(4096 * 117349959766017) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : Int)) :
    Q 65536 (-480665435201605623 : Int) := h
theorem chain_rounds_15 (h : Q 65536 (cz (gr 15 65536), 65536 - 31)) : Q 65536 ((1, 65505) : Nat × Nat) := h
theorem chain_rounds_16 (h : Q 65536 (cz (gr 16 65536), 65536 - 31)) : Q 65536 ((1, 65505) : Nat × Nat) := h
theorem chain_rounds_17 (h : Q 65536 (cz (gr 17 65536), 65536 - 31)) : Q 65536 ((1, 65505) : Nat × Nat) := h
theorem guard_65535 (h : Q 65536 ch_g0) : Q 65536 ch_one := h
theorem guard_65536 (h : Q 65536 ch_g1) : Q 65536 ch_one := h
theorem guard_65537 (h : Q 65536 ch_g2) : Q 65536 ch_one := h
theorem guard_fix (h : Q 65536 ch_gf) : Q 65536 ch_gf' := h
theorem chain_unheld (h : Q 65536 ch_ax) : Q 65536 ch_ax' := h
theorem chain_nested (h : Q 65536 ch_ns) : Q 65536 ch_one := h
theorem chain_refused (h : Q 65536 ch_ks) : Q 65536 ch_one := h
noncomputable def ch_ks2 : Nat × Nat := (if (0 : Int) ≤ 5000 * 14 - 1 then 1 else 0, 65536 - 31)
noncomputable def ch_km : Fin (65536 + 1) :=
  Option.casesOn (motive := fun _ => Fin (65536 + 1))
    (Nat.casesOn (motive := fun _ => Option Nat) (65536 - 1) none (fun _ => some 0)) ⟨0, by decide⟩
    (fun _ => ⟨1, by decide⟩)
theorem chain_refused_small (h : Q 65536 ch_ks2) : Q 65536 ch_one := h
theorem chain_motive (h : Q 65536 ch_km) : Q 65536 (⟨1, by decide⟩ : Fin (65536 + 1)) := h
noncomputable def ch_km2 : Fin (65536 + 1) := cond (isz (65536 - 1)) ⟨0, by decide⟩ ⟨1, by decide⟩
theorem chain_motive2 (h : Q 65536 ch_km2) : Q 65536 (⟨1, by decide⟩ : Fin (65536 + 1)) := h

end RLI434L
