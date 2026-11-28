import Init

/- The bitwise Fin case of the transport pass (tests/fin_transport_bitwise.v and
   tests/fin_transport_bitwise_absent.v; README, "Transport of proof arguments across Nat literals"). Each theorem
   passes a proof of `v ≤ a` (or `v = a`) where `v ≤ d` is expected, `a` and `d` closed terms of the same value,
   most of them `UInt8.ofNatLT k _` against `UInt8.ofNat e`, whose Fin pair is `k` against `e % 2 ^ 8`. The
   theorems are exported in four groups, each one range of export lines: (a) the entries of the per-fix controls;
   (b) every other entry whose values, operands and shifts are below 65535; (c) the budget entries, each with
   terms of its own; (d) the entries with a value, operand or shift of 65535 or more. `noofnat` is exported alone
   (dumps/lean434/bitwise_noofnat.ndjson). -/

set_option maxRecDepth 8192

namespace RLI434B

macro "repeatSucc " n:num t:term : term => do
  let mut e := t
  for _ in [:n.getNat] do e ← `(Nat.succ $e)
  return e

/- (a) The parseFirstByte roots' Fin value `BitVec.toNat 8 (UInt8.toBitVec 224) &&& BitVec.toNat 8
   (UInt8.toBitVec 128)` of `(224 : UInt8) &&& 128`. UInt8's own `&&&` is `BitVec.and`, whose proof
   `Nat.and_lt_two_pow` brings `Nat.mul_add_div._f` into the export, which Rocq's kernel checks in about 1,500 s;
   these entries use an instance of the same shape, `myAnd8`, whose value is `UInt8.ofNat (x.toNat &&& y.toNat)`.
   The two UInt32 entries' kernel conversion outlasts a short entry limit. -/
def myAnd8 : AndOp UInt8 := ⟨fun a b => UInt8.ofNat (a.toBitVec.toNat &&& b.toBitVec.toNat)⟩
theorem and_224 (v : UInt8) (h : v = 128) : v = @HAnd.hAnd UInt8 UInt8 UInt8 (@instHAndOfAndOp UInt8 myAnd8) 224 128 :=
  h
theorem u32_and (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ UInt32.ofNat (255 &&& 127) := h
theorem u32_lor (v : UInt32) (h : v ≤ UInt32.ofNatLT 255 (by decide)) : v ≤ UInt32.ofNat (255 ||| 0) := h

/- (b) The two forms of a row, and three rows. -/
theorem land_fun (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (Nat.land 255 127) := h
theorem land_class (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (255 &&& 127) := h
theorem lor_class (v : UInt8) (h : v ≤ UInt8.ofNatLT 255 (by decide)) : v ≤ UInt8.ofNat (255 ||| 127) := h
theorem xor_both (v : UInt8) (h : v ≤ UInt8.ofNatLT 240 (by decide)) : v ≤ UInt8.ofNat (255 ^^^ 15) := h

/- and_224's two terms again; the widths of the isInvalidContinuationByte and parseFirstByte_eq_done roots. -/
theorem and_224_again (v : UInt8) (h : v = 128) :
    v = @HAnd.hAnd UInt8 UInt8 UInt8 (@instHAndOfAndOp UInt8 myAnd8) 224 128 := h
theorem width_8 (v : BitVec 8) (h : v = BitVec.ofNat (2 + 6) 128) : v = (128 : BitVec 8) := h
theorem width_8b (v : BitVec 8) (h : v = BitVec.ofNat (1 + 7) 128) : v = (128 : BitVec 8) := h

/- The class function at another instance: one the head reduction takes to `Nat.land`, one that stops at a
   match. -/
def myAnd : AndOp Nat := Nat.instAndOp
def matchAnd : AndOp Nat := ⟨fun a b => match b with | 0 => 0 | n + 1 => Nat.land a (n + 1)⟩
theorem land_myinst (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) :
    v ≤ UInt8.ofNat (@HAnd.hAnd Nat Nat Nat (@instHAndOfAndOp Nat myAnd) 255 127) := h
theorem land_matchinst (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) :
    v ≤ UInt8.ofNat (@HAnd.hAnd Nat Nat Nat (@instHAndOfAndOp Nat matchAnd) 255 127) := h

/- Truncated subtraction, a division by 0, and the shifts. -/
theorem sub_127 (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (200 - 73) := h
theorem sub_trunc (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (5 - 7) := h
theorem div_127 (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (254 / 2) := h
theorem div_zero (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (127 / 0) := h
theorem shl_6 (v : UInt8) (h : v ≤ UInt8.ofNatLT 192 (by decide)) : v ≤ UInt8.ofNat (3 <<< 6) := h
theorem shl_15 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (1 <<< 15) := h
theorem shl_17 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (1 <<< 17) := h
theorem shl_zero (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (0 <<< 17) := h

/- An operand with no value: both sides hold `axN &&& 255`, so that Lean converts them. -/
axiom axN : Nat
theorem land_axiom (v : UInt8)
    (h : v ≤ UInt8.ofNatLT ((axN &&& 255) % 256) (Nat.mod_lt (axN &&& 255) (by decide : (256 : Nat) > 0))) :
    v ≤ UInt8.ofNat (axN &&& 255) := h

/- A Nat form over an operand only a row or the head reduction reads. -/
theorem natrow_add (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat ((255 &&& 127) + 0) := h
theorem natrow_succ (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) :
    v ≤ UInt8.ofNat (Nat.succ (UInt8.toBitVec 126).toNat) := h

/- Head reduction to a form the reader reads, and where it stops: a match, a recursion, a projection of a
   match. -/
theorem succ_head (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (id (Nat.succ 126)) := h
theorem stop_ite (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) :
    v ≤ UInt8.ofNat (if (1 : Nat) < 2 then 127 else 127) := h
theorem stop_gcd (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (Nat.gcd 254 127) := h
theorem gcd_value (v : UInt32) (h : v ≤ UInt32.ofNatLT (Nat.gcd 254 127) (by decide)) : v ≤ 127 := h
def pairN (_ : Nat) : Nat × Nat := if (1 : Nat) < 2 then (127, 0) else (127, 1)
def projN (x : Nat) : Nat := (pairN x).1
theorem stop_projv (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (projN 0) := h

/- A head reduction of 63, 64 and 65 steps: two a level (the unfolding and its binder), one for the let. -/
def k0 (_ : Nat) : Nat := 127
def k1 (x : Nat) : Nat := k0 x
def k2 (x : Nat) : Nat := k1 x
def k3 (x : Nat) : Nat := k2 x
def k4 (x : Nat) : Nat := k3 x
def k5 (x : Nat) : Nat := k4 x
def k6 (x : Nat) : Nat := k5 x
def k7 (x : Nat) : Nat := k6 x
def k8 (x : Nat) : Nat := k7 x
def k9 (x : Nat) : Nat := k8 x
def k10 (x : Nat) : Nat := k9 x
def k11 (x : Nat) : Nat := k10 x
def k12 (x : Nat) : Nat := k11 x
def k13 (x : Nat) : Nat := k12 x
def k14 (x : Nat) : Nat := k13 x
def k15 (x : Nat) : Nat := k14 x
def k16 (x : Nat) : Nat := k15 x
def k17 (x : Nat) : Nat := k16 x
def k18 (x : Nat) : Nat := k17 x
def k19 (x : Nat) : Nat := k18 x
def k20 (x : Nat) : Nat := k19 x
def k21 (x : Nat) : Nat := k20 x
def k22 (x : Nat) : Nat := k21 x
def k23 (x : Nat) : Nat := k22 x
def k24 (x : Nat) : Nat := k23 x
def k25 (x : Nat) : Nat := k24 x
def k26 (x : Nat) : Nat := k25 x
def k27 (x : Nat) : Nat := k26 x
def k28 (x : Nat) : Nat := k27 x
def k29 (x : Nat) : Nat := k28 x
def k30 (x : Nat) : Nat := k29 x
def k31 (x : Nat) : Nat := k30 x
theorem fb_63 (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (let y := 0; k30 y) := h
theorem fb_64 (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (k31 0) := h
theorem fb_65 (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (let y := 0; k31 y) := h

/- Parameters compared by value: a record of one field over `Fin 256` with a Nat parameter. -/
structure W (n : Nat) where
  val : Fin 256

def W.ofA (n : Nat) (x : Nat) (h : x < 256) : W n := ⟨⟨x, h⟩⟩
def W.ofB (n : Nat) (x : Nat) : W n := ⟨Fin.ofNat 256 x⟩
theorem lt127 : 127 < 256 := by decide

theorem w_1023 (v : W 1023) (h : v = W.ofA (1020 + 3) 127 lt127) : v = W.ofB 1023 127 := h
theorem w_1024 (v : W 1024) (h : v = W.ofA (1020 + 4) 127 lt127) : v = W.ofB 1024 127 := h
theorem w_1025 (v : W 1025) (h : v = W.ofA (1020 + 5) 127 lt127) : v = W.ofB 1025 127 := h
theorem w_bsub (v : W 1024) (h : v = W.ofA (1025 - 1) 127 lt127) : v = W.ofB 1024 127 := h
theorem w_bxor (v : W 1024) (h : v = W.ofA (1025 ^^^ 1) 127 lt127) : v = W.ofB 1024 127 := h
theorem w_mod_0 (v : W 1024) (h : v = W.ofA (1024 % 0) 127 lt127) : v = W.ofB 1024 127 := h
theorem w_mod_1023 (v : W 1) (h : v = W.ofA (1024 % 1023) 127 lt127) : v = W.ofB 1 127 := h
theorem w_mod_1024 (v : W 1023) (h : v = W.ofA (1023 % 1024) 127 lt127) : v = W.ofB 1023 127 := h
theorem w_mod_1025 (v : W 1024) (h : v = W.ofA (1024 % 1025) 127 lt127) : v = W.ofB 1024 127 := h
theorem w_match (v : W 1024) (h : v = W.ofA (match (0 : Nat) with | 0 => 1024 | _ => 0) 127 lt127) :
    v = W.ofB 1024 127 := h

/- A record whose one field is a variable's type: its parameters are no Nat terms, and it is no data record. -/
structure Box (α : Type) where
  val : α

def boxP (_ : Nat) : Box (Fin 256) := ⟨⟨44, by decide⟩⟩
def boxQ (_ : Nat) : Box (Fin (2 ^ 8)) := ⟨⟨300 % 2 ^ 8, by decide⟩⟩
theorem box_param (v : Box (Fin 256)) (h : v = boxP 0) : v = boxQ 0 := h

/- The data-record gate of the first scan: none of these entries holds a data record, a Nat operation or a
   literal of 4096 or more, so the pass does not run on them. -/
def boxA (_ : Nat) : Box (Fin 256) := ⟨⟨44, by decide⟩⟩
def boxB (_ : Nat) : Box (Fin 256) := ⟨⟨300 % 256, by decide⟩⟩
theorem gate_box (v : Box (Fin 256)) (h : v = boxA 0) : v = boxB 0 := h

structure PT : Type where
  p : True

def ptz : PT := ⟨trivial⟩
theorem field_pt (v : Box (Fin 256)) (_ : ptz = ptz) (h : v = boxA 0) : v = boxB 0 := h

structure P2 where
  a : Nat
  b : Nat

def pz : P2 := ⟨0, 0⟩
theorem field_p2 (v : Box (Fin 256)) (_ : pz = pz) (h : v = boxA 0) : v = boxB 0 := h

def isB (_ : UInt8) : Prop := True
def u8c : UInt8 := 5
def boxG (_ : isB u8c) : Box (Fin 256) := ⟨⟨44, by decide⟩⟩
theorem gate_glob (v : Box (Fin 256)) (h : v = boxG trivial) : v = boxB 0 := h

/- A `%` at an instance that is not `Nat.instMod`, which the head reduction takes to a match. -/
def matchMod : Mod Nat := ⟨fun a b => match b with | 0 => a | n + 1 => Nat.mod a (n + 1)⟩
theorem badmod_match (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) :
    v ≤ UInt8.ofNat (@HMod.hMod Nat Nat Nat (@instHMod Nat matchMod) 127 200) := h

/- (c) The budget entries. -/
theorem bud_and (v : UInt8) (h : v = 192) :
    v = @HAnd.hAnd UInt8 UInt8 UInt8 (@instHAndOfAndOp UInt8 myAnd8) 224 192 := h
theorem lt126 : 126 < 256 := by decide
theorem bud_w (v : W 1024) (h : v = W.ofA (1012 + 12) 126 lt126) : v = W.ofB 1024 126 := h
def m0 (_ : Nat) : Nat := 125
def m1 (x : Nat) : Nat := m0 x
def m2 (x : Nat) : Nat := m1 x
def m3 (x : Nat) : Nat := m2 x
def m4 (x : Nat) : Nat := m3 x
def m5 (x : Nat) : Nat := m4 x
def m6 (x : Nat) : Nat := m5 x
def m7 (x : Nat) : Nat := m6 x
def m8 (x : Nat) : Nat := m7 x
def m9 (x : Nat) : Nat := m8 x
def m10 (x : Nat) : Nat := m9 x
def m11 (x : Nat) : Nat := m10 x
def m12 (x : Nat) : Nat := m11 x
def m13 (x : Nat) : Nat := m12 x
def m14 (x : Nat) : Nat := m13 x
def m15 (x : Nat) : Nat := m14 x
def m16 (x : Nat) : Nat := m15 x
def m17 (x : Nat) : Nat := m16 x
def m18 (x : Nat) : Nat := m17 x
def m19 (x : Nat) : Nat := m18 x
def m20 (x : Nat) : Nat := m19 x
def m21 (x : Nat) : Nat := m20 x
def m22 (x : Nat) : Nat := m21 x
def m23 (x : Nat) : Nat := m22 x
def m24 (x : Nat) : Nat := m23 x
def m25 (x : Nat) : Nat := m24 x
def m26 (x : Nat) : Nat := m25 x
def m27 (x : Nat) : Nat := m26 x
def m28 (x : Nat) : Nat := m27 x
def m29 (x : Nat) : Nat := m28 x
def m30 (x : Nat) : Nat := m29 x
def m31 (x : Nat) : Nat := m30 x
theorem bud_fb (v : UInt8) (h : v ≤ UInt8.ofNatLT 125 (by decide)) : v ≤ UInt8.ofNat (m31 0) := h

/- const_only holds no OfNat.ofNat at a data record, only constants of type UInt8, and a ballast that only the
   entry's own scan reads (eight unary literals of 1000), so that its entry part is its largest part. -/
def b128 : UInt8 := 128
def b224 : UInt8 := 224
def bal8 (_ _ _ _ _ _ _ _ : Nat) : Nat := 0
def ignoreNat (_ : Nat) : Nat := 0
macro "ballastB" : term =>
  `(bal8 (repeatSucc 1000 0) (repeatSucc 1000 0) (repeatSucc 1000 0) (repeatSucc 1000 0) (repeatSucc 1000 0)
      (repeatSucc 1000 0) (repeatSucc 1000 0) (repeatSucc 1000 0))
theorem const_only (v : UInt8) (_b : ignoreNat ballastB = 0) (h : v = b128) :
    v = @HAnd.hAnd UInt8 UInt8 UInt8 (@instHAndOfAndOp UInt8 myAnd8) b224 b128 := h

/- (d) A value, operand or shift of 65535 or more. -/
theorem land_65535 (v : UInt8) (h : v ≤ UInt8.ofNatLT 255 (by decide)) : v ≤ UInt8.ofNat (65535 &&& 255) := h
theorem land_65536 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (65536 &&& 255) := h
theorem land_65537 (v : UInt8) (h : v ≤ UInt8.ofNatLT 1 (by decide)) : v ≤ UInt8.ofNat (65537 &&& 255) := h
theorem lor_65535 (v : UInt8) (h : v ≤ UInt8.ofNatLT 255 (by decide)) : v ≤ UInt8.ofNat (65535 ||| 0) := h
theorem lor_65536 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (65536 ||| 0) := h
theorem xor_65535 (v : UInt8) (h : v ≤ UInt8.ofNatLT 255 (by decide)) : v ≤ UInt8.ofNat (65535 ^^^ 0) := h
theorem xor_65536 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (65536 ^^^ 0) := h
theorem sub_65536 (v : UInt8) (h : v ≤ UInt8.ofNatLT 127 (by decide)) : v ≤ UInt8.ofNat (65536 - 65409) := h
theorem div_65536 (v : UInt8) (h : v ≤ UInt8.ofNatLT 128 (by decide)) : v ≤ UInt8.ofNat (65536 / 512) := h
theorem shl_16 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (1 <<< 16) := h
theorem shr_15 (v : UInt8) (h : v ≤ UInt8.ofNatLT 1 (by decide)) : v ≤ UInt8.ofNat (65535 >>> 15) := h
theorem shr_16 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (65535 >>> 16) := h
theorem shr_17 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (65535 >>> 17) := h
theorem shr_18 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (65535 >>> 18) := h
theorem shr_big (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ UInt8.ofNat (5 >>> 65536) := h
theorem w_sub (v : W 1024) (h : v = W.ofA (65535 - 64511) 127 lt127) : v = W.ofB 1024 127 := h

/- A statement with an application headed by a constant (the Prelude's Bool negation) and no OfNat.ofNat in its
   closure. -/
theorem noofnat (b : Bool) (h : (!b) = false) : (!b) = false := h

end RLI434B
