import Init

/- Casts at relevant positions in the values of entries whose type is a proposition (README, "Transport of proof
   arguments across Nat literals", the item on relevant positions; tests/relcast.v, tests/relcast_absent.v,
   tests/relcast_refused.v). The pair is String.length_utf8EncodeChar's: `UInt32.decLe c.val (UInt32.ofNatLT 65535 _)`
   where `ite` expects `Decidable (c.val ≤ 65535)`, whose two Fin values are 65535 and 65535 % 2 ^ 32; Rocq's
   kernel converts that pair on the unary Nat far longer than a short entry limit. The fixtures that only need the
   pass's log use the pairs of the records `W` (over `Fin 5`), `W1` (over `Fin 2`) and `W2` (over `Fin 2048`),
   `wk k _` against `mkW k`, `w1 _` against `mkW1` and `W2.lit v _` against `mkW2 v`, which the kernel converts at
   once (`k % 5`, `1 % 2`, `v % 2048` below the divisor).
   Every instance is written out (no `inferInstanceAs`, whose auxiliary definition would hold the pair in a data
   definition). The chains F*, S*, I* and the conjunction of `True` in `BigP` were written by a script. -/
namespace RLI434RC

set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000

theorem lt65535 : 65535 < UInt32.size := by decide
theorem lt65535b : 65535 < UInt32.size := by decide
theorem lt127 : 127 < UInt32.size := by decide
theorem lt65536 : 65536 < UInt32.size := by decide
theorem lt65537 : 65537 < UInt32.size := by decide

/- The cheap pairs. -/
structure W where
  val : Fin 5
def wk (n : Nat) (h : n < 5) : W := ⟨⟨n, h⟩⟩
def mkW (n : Nat) : W := ⟨⟨n % 5, Nat.mod_lt _ (by decide)⟩⟩
instance : LE W := ⟨fun a b => a.val.val ≤ b.val.val⟩
instance decLeW (a b : W) : Decidable (a ≤ b) := Nat.decLe a.val.val b.val.val
structure W2 where
  val : Fin 2048
def W2.lit (n : Nat) (h : n < 2048) : W2 := ⟨⟨n, h⟩⟩
def mkW2 (n : Nat) : W2 := ⟨⟨n % 2048, Nat.mod_lt _ (by decide)⟩⟩
instance : LE W2 := ⟨fun a b => a.val.val ≤ b.val.val⟩
instance decLeW2 (a b : W2) : Decidable (a ≤ b) := Nat.decLe a.val.val b.val.val
structure W1 where
  val : Fin 2
theorem l12 : 1 < 2 := by decide
theorem m12 : 1 % 2 < 2 := Nat.mod_lt _ (by decide)
def w1 (h : 1 < 2) : W1 := ⟨⟨1, h⟩⟩
def mkW1 (_ : Unit) : W1 := ⟨⟨1 % 2, m12⟩⟩
instance : LE W1 := ⟨fun a b => a.val.val ≤ b.val.val⟩
instance decLeW1 (a b : W1) : Decidable (a ≤ b) := Nat.decLe a.val.val b.val.val
theorem lw0 : 0 < 5 := by decide
theorem lw1 : 1 < 5 := by decide
theorem lw2 : 2 < 5 := by decide
theorem lw3 : 3 < 5 := by decide
theorem lw4 : 4 < 5 := by decide
theorem lt2000 : 2000 < 2048 := by decide
theorem lt2001 : 2001 < 2048 := by decide
theorem lt2040 : 2040 < 2048 := by decide

/- An alias of a proposition and of a data type. -/
def PA : Prop := True
def NA : Type := Nat

/- Domains that are no inductive type as declared: an alias, a product. -/
def DecA (p : Prop) : Type := Decidable p
def useA (p : Prop) (_ : DecA p) : Nat := 0
def useP (p : Prop) (_ : Unit → Decidable p) : Nat := 0

/- A function type that takes 71 unfoldings to expose (F70), a sort that takes 71 (S70), an argument type that
   takes 71 (I70). -/
def F0 : Type := (p : Prop) → Decidable p → Nat
def F1 : Type := F0
def F2 : Type := F1
def F3 : Type := F2
def F4 : Type := F3
def F5 : Type := F4
def F6 : Type := F5
def F7 : Type := F6
def F8 : Type := F7
def F9 : Type := F8
def F10 : Type := F9
def F11 : Type := F10
def F12 : Type := F11
def F13 : Type := F12
def F14 : Type := F13
def F15 : Type := F14
def F16 : Type := F15
def F17 : Type := F16
def F18 : Type := F17
def F19 : Type := F18
def F20 : Type := F19
def F21 : Type := F20
def F22 : Type := F21
def F23 : Type := F22
def F24 : Type := F23
def F25 : Type := F24
def F26 : Type := F25
def F27 : Type := F26
def F28 : Type := F27
def F29 : Type := F28
def F30 : Type := F29
def F31 : Type := F30
def F32 : Type := F31
def F33 : Type := F32
def F34 : Type := F33
def F35 : Type := F34
def F36 : Type := F35
def F37 : Type := F36
def F38 : Type := F37
def F39 : Type := F38
def F40 : Type := F39
def F41 : Type := F40
def F42 : Type := F41
def F43 : Type := F42
def F44 : Type := F43
def F45 : Type := F44
def F46 : Type := F45
def F47 : Type := F46
def F48 : Type := F47
def F49 : Type := F48
def F50 : Type := F49
def F51 : Type := F50
def F52 : Type := F51
def F53 : Type := F52
def F54 : Type := F53
def F55 : Type := F54
def F56 : Type := F55
def F57 : Type := F56
def F58 : Type := F57
def F59 : Type := F58
def F60 : Type := F59
def F61 : Type := F60
def F62 : Type := F61
def F63 : Type := F62
def F64 : Type := F63
def F65 : Type := F64
def F66 : Type := F65
def F67 : Type := F66
def F68 : Type := F67
def F69 : Type := F68
def F70 : Type := F69
def g70 : F70 := fun _ _ => 0
def S0 : Type := Prop
def S1 : Type := S0
def S2 : Type := S1
def S3 : Type := S2
def S4 : Type := S3
def S5 : Type := S4
def S6 : Type := S5
def S7 : Type := S6
def S8 : Type := S7
def S9 : Type := S8
def S10 : Type := S9
def S11 : Type := S10
def S12 : Type := S11
def S13 : Type := S12
def S14 : Type := S13
def S15 : Type := S14
def S16 : Type := S15
def S17 : Type := S16
def S18 : Type := S17
def S19 : Type := S18
def S20 : Type := S19
def S21 : Type := S20
def S22 : Type := S21
def S23 : Type := S22
def S24 : Type := S23
def S25 : Type := S24
def S26 : Type := S25
def S27 : Type := S26
def S28 : Type := S27
def S29 : Type := S28
def S30 : Type := S29
def S31 : Type := S30
def S32 : Type := S31
def S33 : Type := S32
def S34 : Type := S33
def S35 : Type := S34
def S36 : Type := S35
def S37 : Type := S36
def S38 : Type := S37
def S39 : Type := S38
def S40 : Type := S39
def S41 : Type := S40
def S42 : Type := S41
def S43 : Type := S42
def S44 : Type := S43
def S45 : Type := S44
def S46 : Type := S45
def S47 : Type := S46
def S48 : Type := S47
def S49 : Type := S48
def S50 : Type := S49
def S51 : Type := S50
def S52 : Type := S51
def S53 : Type := S52
def S54 : Type := S53
def S55 : Type := S54
def S56 : Type := S55
def S57 : Type := S56
def S58 : Type := S57
def S59 : Type := S58
def S60 : Type := S59
def S61 : Type := S60
def S62 : Type := S61
def S63 : Type := S62
def S64 : Type := S63
def S65 : Type := S64
def S66 : Type := S65
def S67 : Type := S66
def S68 : Type := S67
def S69 : Type := S68
def S70 : Type := S69
def p70 : S70 := True
def I0 : Type := (c : Char) → Decidable (c.val ≤ UInt32.ofNatLT 65535 lt65535)
def I1 : Type := I0
def I2 : Type := I1
def I3 : Type := I2
def I4 : Type := I3
def I5 : Type := I4
def I6 : Type := I5
def I7 : Type := I6
def I8 : Type := I7
def I9 : Type := I8
def I10 : Type := I9
def I11 : Type := I10
def I12 : Type := I11
def I13 : Type := I12
def I14 : Type := I13
def I15 : Type := I14
def I16 : Type := I15
def I17 : Type := I16
def I18 : Type := I17
def I19 : Type := I18
def I20 : Type := I19
def I21 : Type := I20
def I22 : Type := I21
def I23 : Type := I22
def I24 : Type := I23
def I25 : Type := I24
def I26 : Type := I25
def I27 : Type := I26
def I28 : Type := I27
def I29 : Type := I28
def I30 : Type := I29
def I31 : Type := I30
def I32 : Type := I31
def I33 : Type := I32
def I34 : Type := I33
def I35 : Type := I34
def I36 : Type := I35
def I37 : Type := I36
def I38 : Type := I37
def I39 : Type := I38
def I40 : Type := I39
def I41 : Type := I40
def I42 : Type := I41
def I43 : Type := I42
def I44 : Type := I43
def I45 : Type := I44
def I46 : Type := I45
def I47 : Type := I46
def I48 : Type := I47
def I49 : Type := I48
def I50 : Type := I49
def I51 : Type := I50
def I52 : Type := I51
def I53 : Type := I52
def I54 : Type := I53
def I55 : Type := I54
def I56 : Type := I55
def I57 : Type := I56
def I58 : Type := I57
def I59 : Type := I58
def I60 : Type := I59
def I61 : Type := I60
def I62 : Type := I61
def I63 : Type := I62
def I64 : Type := I63
def I65 : Type := I64
def I66 : Type := I65
def I67 : Type := I66
def I68 : Type := I67
def I69 : Type := I68
def I70 : Type := I69
def gi : I70 := fun c => UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)

/- The proof whose type holds Lean's instance, at a proposition the caller names (h_pair). -/
theorem helper {P : Prop} (d : Decidable P) : @ite Nat P d 1 2 = @ite Nat P d 1 2 := rfl

/- A proof whose type holds the W pair at the instance only, and a Nat pair (relhole_no_fin). -/
axiom hU (x : W) : @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2 = 2 ^ 40

/- Entries with no value: an inductive type and an axiom whose types hold the W pair. -/
inductive KindInd : Prop where
  | mk (x : W) : @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2 = 1 → KindInd
axiom kind_axiom (x : W) : @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2 = @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2

/- A relevant inductive type in a universe of its own, and one in a universe that is a maximum. -/
structure PBox.{w} (p : Prop) : Type w where
  val : PUnit.{w+1}
def usePBox.{w} (p : Prop) (_ : PBox.{w} p) : Nat := 0
structure PBox2.{v, w} (p : Prop) : Type (max v w) where
  val : PUnit.{(max v w) + 1}
def usePBox2.{v, w} (p : Prop) (_ : PBox2.{v, w} p) : Nat := 0
/- A value whose term holds a universe of the entry. -/
def idU.{w} (n : Nat) : Nat := (fun (_ : PUnit.{w+1}) => n) PUnit.unit
/- One argument whose type holds two W pairs, the second through idU (two_holes_one_absent). -/
def dAnd.{w} (x : W) : Decidable (x ≤ wk 3 lw3 ∧ x ≤ wk (idU.{w} 4) lw4) :=
  @instDecidableAnd _ _ (decLeW x (wk 3 lw3)) (decLeW x (wk (idU.{w} 4) lw4))

/- A large closed domain: a conjunction of 300 `True`, then the W pair (detect_arg, detect_total_hi). -/
def BigP : Prop := True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3
def useBig (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) : Nat := 0
def instBig : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ wk 3 lw3) := inferInstance
def instBigOk : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3) := inferInstance
def useBig13 (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) (_ : Decidable (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ wk 3 lw3 ≤ mkW 3)) : Nat := 0

/- The Nat.mod that dumps/lean434/relcast_refused.ndjson plants: its value becomes `fun _ _ => 0` there, and the
   bound below is an axiom, so that its type is all the plant changes. -/
def pmod (x y : Nat) : Nat := x % y
axiom pmod_lt : pmod 127 (2 ^ 32) < 2 ^ 32

/- The first three: tests/relcast.v's first part (no other entry between them). -/
theorem theorem_closed (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
theorem again (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
def data_closed (c : Char) : Nat := @ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2

/- A definition whose type is a proposition, and its consumer. -/
def aux_closed (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
theorem aux_user (c : Char) : True := aux_closed c
/- The two values in the other order. -/
theorem reverse_closed (c : Char) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ UInt32.ofNatLT 65535 lt65535) (UInt32.decLe c.val 65535) 1 2)
/- A proof cast too: the value's own type 2 ^ 39 + 2 ^ 39 = 2 ^ 40 against 2 ^ 40 = 2 ^ 40. -/
theorem keep_sprop (c : Char) (h : 2 ^ 39 + 2 ^ 39 = 2 ^ 40) : 2 ^ 40 = 2 ^ 40 := (fun (_ : Nat) => h) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
theorem head_stop_hit (c : Char) (h : 2 ^ 40 + 2 ^ 40 = 2 ^ 41) : 2 ^ 41 = 2 ^ 41 := (fun (_ : Nat) => h) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
/- The pair in a binder type inside the value, and in the proof of that type. -/
theorem body_type (c : Char) : True := (fun (_ : @ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2 = @ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2) => True.intro) rfl
/- The pair at a lambda's binder, the argument of a redex. -/
theorem beta_visible (c : Char) : True :=
  (fun (_ : Nat) => True.intro)
    ((fun (d : Decidable (c.val ≤ 65535)) => @ite Nat (c.val ≤ 65535) d 1 2) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)))
/- A Fin place that is closed only after beta, and one that beta drops. -/
theorem beta_only (c : Char) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ (fun (y : Nat) => UInt32.ofNat y) (nat_lit 65535)) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
theorem beta_erased (c : Char) : True :=
  (fun (_ : Nat) => True.intro)
    (@ite Nat (c.val ≤ (fun (_ : UInt32) => (100 : UInt32)) (65535 : UInt32)) (UInt32.decLe c.val 100) 1 2)
/- Domains with no Fin place: a bare inductive type, an equality of characters, a Nat literal, a large one. -/
theorem bare_domain (c : Char) : True := (fun (_ : UInt32) => True.intro) (UInt32.ofNatLT 65535 lt65535)
theorem no_fin (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c = c) (decEq c c) 1 2)
theorem literal_only (n : Nat) : True := (fun (_ : Nat) => True.intro) (@ite Nat (n ≤ 65535) (Nat.decLe n 65535) 1 2)
theorem over_double (n : Nat) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (n ≤ 1000000) (Nat.decLe n 1000000) 1 2)
theorem ofnat_2047 : True := (fun (_ : UInt32) => True.intro) (2047 : UInt32)
theorem ofnat_65535 : True := (fun (_ : UInt32) => True.intro) (65535 : UInt32)
/- The pair under Nat.succ. -/
theorem under_succ : True :=
  (fun (_ : Nat) => True.intro)
    (@ite Nat (Nat.succ (UInt32.toNat 65535) ≤ nat_lit 5)
      (Nat.decLe (Nat.succ (UInt32.toNat (UInt32.ofNatLT 65535 lt65535))) (nat_lit 5)) 1 2)
/- Declared domains that are a product, a variable, an alias; a function type and an argument type the pass does
   not read; a sort it does not read. -/
theorem domain_product (c : Char) : True := (fun (_ : Nat) => True.intro) (useP (c.val ≤ 65535) (fun _ => UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)))
theorem domain_var (c : Char) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (@id (Decidable (c.val ≤ 65535)) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535))) 1 2)
theorem domain_alias (c : Char) : True := (fun (_ : Nat) => True.intro) (useA (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)))
theorem opaque_fun_type (c : Char) : True := (fun (_ : Nat) => True.intro) (g70 (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)))
theorem unreadable_argument (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (gi c) 1 2)
theorem unreadable_prop_sort (c : Char) : p70 := (fun (_ : Nat) => (True.intro : p70)) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
/- Aliases of a proposition and of a data type. -/
theorem prop_alias (c : Char) : PA := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
def data_alias (c : Char) : NA := @ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2
/- Open values: the proof of the bound is a variable, on either side. -/
theorem open_actual (c : Char) (h : 65535 < UInt32.size) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 h)) 1 2)
theorem open_expected (c : Char) (h : 65535 < UInt32.size) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ UInt32.ofNatLT 65535 h) (UInt32.decLe c.val 65535) 1 2)
/- No hole: the same instance; the same head with another proof. -/
theorem same_instance (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val 65535) 1 2)
theorem same_head (c : Char) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ UInt32.ofNatLT 65535 lt65535b) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
/- A pair that is no Fin pair (Int), a Nat pair, a Fin pair with a Nat pair. -/
theorem not_fin (c : Char) (i : Int) : True :=
  (fun (_ : Nat) => True.intro)
    (@ite Nat (c.val ≤ 65535 ∧ i ≤ 5) (@instDecidableAnd _ _ (UInt32.decLe c.val 65535) (Int.decLe i (Int.ofNat 5))) 1 2)
theorem nat_only (c : Char) (n : Nat) : True :=
  (fun (_ : Nat) => True.intro)
    (@ite Nat (c.val ≤ 65535 ∧ n ≤ 1099511627776) (@instDecidableAnd _ _ (UInt32.decLe c.val 65535) (Nat.decLe n (2 ^ 40))) 1 2)
theorem mixed_holes (c : Char) (n : Nat) : True :=
  (fun (_ : Nat) => True.intro)
    (@ite Nat (c.val ≤ 65535 ∧ n ≤ 1099511627776) (@instDecidableAnd _ _ (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) (Nat.decLe n (2 ^ 40))) 1 2)
/- The Fin values at the Fin case's ceiling and above it. -/
theorem fin_65536 (c : Char) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65536) (UInt32.decLe c.val (UInt32.ofNatLT 65536 lt65536)) 1 2)
theorem fin_65537 (c : Char) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65537) (UInt32.decLe c.val (UInt32.ofNatLT 65537 lt65537)) 1 2)
/- A proof whose type holds Lean's instance where the expected type holds the cast (h_pair), the other way round
   (relhole_reverse), and at the instance only, beside a Nat pair (relhole_no_fin). -/
theorem h_pair (c : Char) : True :=
  (fun (_ : @ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2 = @ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2) => True.intro)
    (@helper (c.val ≤ UInt32.ofNatLT 65535 lt65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)))
theorem relhole_reverse (c : Char) : True :=
  (fun (_ : @ite Nat (c.val ≤ UInt32.ofNatLT 65535 lt65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2 =
      @ite Nat (c.val ≤ UInt32.ofNatLT 65535 lt65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2) => True.intro)
    (Eq.refl (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2))
theorem relhole_no_fin (x : W) : True :=
  (fun (_ : @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2 = 1099511627776) => True.intro) (hU x)
/- The W pair in the declared type (one the kernel converts at once), and a proof of it. -/
theorem declared_B (x : W) : @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2 = @ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2 := rfl
/- No trigger of the pass. -/
theorem no_trigger (b : Bool) : b = b := rfl
/- The W pair in a relevant inductive type of a universe of its own, of a maximum. -/
theorem higher_domain.{w} (x : W) (_u : PUnit.{w+1}) : True :=
  (fun (_ : Nat) => True.intro) (usePBox.{w} (x ≤ mkW 3) (PBox.mk.{w} (p := x ≤ wk 3 lw3) PUnit.unit))
theorem universe_max.{v, w} (x : W) (_u : PUnit.{(max v w)+1}) : True :=
  (fun (_ : Nat) => True.intro)
    (usePBox2.{v, w} (x ≤ mkW 3) (PBox2.mk.{v, w} (p := x ≤ wk 3 lw3) PUnit.unit))
/- A Fin value that holds a universe of the entry: no lemma; with a second Fin pair beside it. The proof cast is
   the W pair 2. -/
theorem lemma_absent.{w} (x : W) (_u : PUnit.{w+1}) (h : x ≤ wk 2 lw2) : x ≤ mkW 2 :=
  (fun (_ : Nat) => h) (@ite Nat (x ≤ mkW 3) (decLeW x (wk (idU.{w} 3) lw3)) 1 2)
theorem two_holes_one_absent.{w} (x : W) (_u : PUnit.{w+1}) (h : x ≤ wk 2 lw2) : x ≤ mkW 2 :=
  (fun (_ : Nat) => h)
    (@ite Nat (x ≤ mkW 3 ∧ x ≤ mkW 4) (dAnd.{w} x) 1 2)
/- The pair beside a place the pass leaves to the kernel, which outlasts the limit. -/
theorem candidate_limit (c : Char) : True :=
  (fun (_ : Nat) (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
    (@ite Nat (c.val ≤ 65535) (@id (Decidable (c.val ≤ 65535)) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535))) 3 4)
/- The pair of theorem_closed, imported at budgets around max_int / 10. -/
theorem cap_mul (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)

/- The budget rows (tests/relcast.v, under Succeed): one relevant site of a fresh W2 lemma beside an SProp cast
   (rel_arg); 40 sites of one W lemma (rel_own, after rel_own_lib declares it); 20 sites of one fresh W2 lemma
   (rel_total_hi); a large closed domain at one site (detect_arg) and at 13 (detect_total_hi); then an entry whose
   SProp pass's part is pinned (cache_after). -/
theorem rel_arg (b : W2) (x : W) (h : x ≤ wk 1 lw1) : True :=
  (fun (_ : x ≤ mkW 1) (_ : Nat) => True.intro) h (@ite Nat (b ≤ mkW2 2000) (decLeW2 b (W2.lit 2000 lt2000)) 1 2)
theorem rel_own_lib (x : W) : True := (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
theorem rel_own (x : W) (h : x ≤ wk 1 lw1) : True :=
  (fun (_ : x ≤ mkW 1) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) => True.intro) h
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
    (@ite Nat (x ≤ mkW 4) (decLeW x (wk 4 lw4)) 1 2)
theorem rel_total_hi (b : W2) (x : W) (h : x ≤ wk 1 lw1) : True :=
  (fun (_ : x ≤ mkW 1) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) (_ : Nat) => True.intro) h
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
    (@ite Nat (b ≤ mkW2 2001) (decLeW2 b (W2.lit 2001 lt2001)) 1 2)
theorem detect_arg (x : W) (h : x ≤ wk 1 lw1) : x ≤ mkW 1 := (fun (_ : Nat) => h) (useBig instBig)
theorem detect_total_hi (x : W) (h : x ≤ wk 1 lw1) : x ≤ mkW 1 :=
  (fun (_ : Nat) => h) (useBig13 instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBigOk instBig)
theorem cache_after (b : W2) (h : b ≤ W2.lit 2040 lt2040) : b ≤ mkW2 2040 := h

/- For the Job patch relcast-plant.patch (the relcast-fallback Job): a relevant site beside an SProp cast
   (sprop_plant) and alone (no_sprop_plant). -/
theorem sprop_plant (b : W2) (x : W) (h : x ≤ wk 1 lw1) : x ≤ mkW 1 := (fun (_ : Nat) => h) (@ite Nat (b ≤ mkW2 2000) (decLeW2 b (W2.lit 2000 lt2000)) 1 2)
theorem no_sprop_plant (b : W2) : True := (fun (_ : Nat) => True.intro) (@ite Nat (b ≤ mkW2 2000) (decLeW2 b (W2.lit 2000 lt2000)) 1 2)

/- tests/relcast_refused.v: the first relevant argument's Fin value goes through the planted Nat.mod, so its lemma
   is refused; the second is theorem_closed's pair, which the Fin case proves. -/
theorem refused_mod (c : Char) : True := (fun (_ : Nat) (_ : Nat) => True.intro) (@ite Nat (c.val ≤ id (UInt32.ofBitVec (BitVec.ofFin (Fin.mk (pmod 127 (2 ^ 32)) pmod_lt)))) (UInt32.decLe c.val (UInt32.ofNatLT 127 lt127)) 1 2) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
theorem refused_mod_sprop (c : Char) (x : W) (h : x ≤ wk 1 lw1) : x ≤ mkW 1 :=
  (fun (_ : Nat) (_ : Nat) => h) (@ite Nat (c.val ≤ id (UInt32.ofBitVec (BitVec.ofFin (Fin.mk (pmod 127 (2 ^ 32)) pmod_lt)))) (UInt32.decLe c.val (UInt32.ofNatLT 127 lt127)) 1 2) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)
/- A small value the kernel refuses after the plant (its proof of pmod 3 8 = 3, raw literals), beside one
   relevant cast of the W1 pair, padded with `id` and `Nat.succ`. -/
theorem refused_255 (y : W1) : True :=
  (fun (_ : pmod (nat_lit 3) (nat_lit 8) = nat_lit 3) (_ : Nat) (_ : Nat) => True.intro) rfl (@id Nat (Nat.succ (nat_lit 0)))
    (@ite Nat (y ≤ mkW1 ()) (decLeW1 y (w1 l12)) 1 2)
theorem refused_256 (y : W1) : True :=
  (fun (_ : pmod (nat_lit 3) (nat_lit 8) = nat_lit 3) (_ : Nat) (_ : Nat) => True.intro) rfl (Nat.succ (Nat.succ (Nat.succ (nat_lit 0))))
    (@ite Nat (y ≤ mkW1 ()) (decLeW1 y (w1 l12)) 1 2)
theorem refused_257 (y : W1) : True :=
  (fun (_ : pmod (nat_lit 3) (nat_lit 8) = nat_lit 3) (_ : Nat) (_ : Nat) => True.intro) rfl (@id Nat (Nat.succ (Nat.succ (nat_lit 0))))
    (@ite Nat (y ≤ mkW1 ()) (decLeW1 y (w1 l12)) 1 2)
/- After refused_mod: the pair of its second argument. -/
theorem after_refused (c : Char) : True := (fun (_ : Nat) => True.intro) (@ite Nat (c.val ≤ 65535) (UInt32.decLe c.val (UInt32.ofNatLT 65535 lt65535)) 1 2)


/- V-mismatch (tests/relcast.v's tail), each beside a control the pass casts: a record parameter of the two
   chains that the parameter reader cannot read (4096 against 2048 + 2048: param_mismatch; the same term:
   param_match); a Fin bound the same way in a record without parameter (bound_mismatch, bound_match); a Fin value
   the Fin case's reader cannot read, a match it does not reduce (opaque_value), and one it reads (readable_value).
   The kernel converts each pair at once. -/
structure W4 (n : Nat) where
  val : Fin n
def wk4 (n k : Nat) (h : k < n) : W4 n := ⟨⟨k, h⟩⟩
def mk4 (n k : Nat) (h : 0 < n) : W4 n := ⟨⟨k % n, Nat.mod_lt _ h⟩⟩
instance : LE (W4 n) := ⟨fun a b => a.val.val ≤ b.val.val⟩
instance decLe4 (a b : W4 n) : Decidable (a ≤ b) := Nat.decLe a.val.val b.val.val
theorem l3_4096 : 3 < 4096 := by decide
theorem p4096 : 0 < 4096 := by decide
theorem p2048 : 0 < 2048 + 2048 := by decide
theorem param_mismatch (x : W4 4096) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ (mk4 (2048 + 2048) 3 p2048 : W4 4096)) (decLe4 x (wk4 4096 3 l3_4096)) 1 2)
theorem param_match (x : W4 4096) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ mk4 4096 3 p4096) (decLe4 x (wk4 4096 3 l3_4096)) 1 2)
structure W5 where
  val : Fin 4096
def wk5 (k : Nat) (h : k < 4096) : W5 := ⟨⟨k, h⟩⟩
def mk5 (k : Nat) : W5 := ⟨⟨k % 4096, Nat.mod_lt _ (by decide)⟩⟩
def mk5b (k : Nat) : W5 := ⟨(⟨k % 4096, Nat.mod_lt _ (by decide)⟩ : Fin (2048 + 2048))⟩
instance : LE W5 := ⟨fun a b => a.val.val ≤ b.val.val⟩
instance decLe5 (a b : W5) : Decidable (a ≤ b) := Nat.decLe a.val.val b.val.val
theorem bound_mismatch (x : W5) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ mk5b 7) (decLe5 x (wk5 7 (by decide))) 1 2)
theorem bound_match (x : W5) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ mk5 7) (decLe5 x (wk5 7 (by decide))) 1 2)
def f3 (n : Nat) : Nat := match n with
  | 0 => 3
  | _ + 1 => 3
theorem lf3 : f3 0 < 5 := by decide
theorem l21 : 2 + 1 < 5 := by decide
theorem opaque_value (x : W) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ mkW 3) (decLeW x (wk (f3 0) lf3)) 1 2)
theorem readable_value (x : W) : True :=
  (fun (_ : Nat) => True.intro) (@ite Nat (x ≤ mkW 3) (decLeW x (wk (2 + 1) l21)) 1 2)
/- E-sort-other: an entry whose type's sort is its universe u. Under Lean Upfront Instantiation both instances are
   declared: u a level (a data definition, no relevant pass) and u := SProp (a proposition, the cast). -/
def sortpoly.{u} (α : Sort u) (x : W) (h : α) : α := (fun (_ : Nat) => h) (@ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2)
/- V-mismatch, different record chains: `ign` ignores its arguments, so `ign W (mkW 3)` and `ign W5 (mk5 3)` are
   convertible while the pair at their second arguments is of two records (W and W5): record_mismatch; the control
   record_match has the W pair there, cast. -/
def ign (T : Type) (_ : T) : Prop := True
def dIgnW : Decidable (ign W (mkW 3)) := isTrue trivial
def dIgnWk : Decidable (ign W (wk 3 lw3)) := isTrue trivial
theorem record_mismatch : True := (fun (_ : Nat) => True.intro) (@ite Nat (ign W5 (mk5 3)) dIgnW 1 2)
theorem record_match : True := (fun (_ : Nat) => True.intro) (@ite Nat (ign W (mkW 3)) dIgnWk 1 2)

end RLI434RC
