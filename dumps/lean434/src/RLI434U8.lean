/- UInt8, UInt16 and Fin literals as Lean writes them: each `le` theorem passes a proof against a value built with
   `ofNatLT` (or `⟨44, _⟩`) where the literal is expected, the Fin case of the transport pass
   (tests/fin_transport_ceiling.v). -/

theorem RLI434U8.toNat_300 : (300 : UInt8).toNat = 44 := by decide

/- (300 : UInt8) is 300 % 2 ^ 8 = 44: a dividend above its divisor. -/
theorem RLI434U8.le_300 (v : UInt8) (h : v ≤ UInt8.ofNatLT 44 (by decide)) : v ≤ (300 : UInt8) := h

theorem RLI434U8.le_65535 (v : UInt8) (h : v ≤ UInt8.ofNatLT 255 (by decide)) : v ≤ (65535 : UInt8) := h

theorem RLI434U8.le16_300 (v : UInt16) (h : v ≤ UInt16.ofNatLT 300 (by decide)) : v ≤ (300 : UInt16) := h

theorem RLI434U8.le16_65535 (v : UInt16) (h : v ≤ UInt16.ofNatLT 65535 (by decide)) : v ≤ (65535 : UInt16) := h

/- Fin.ofNat 256 300 with Lean's own NeZero instance, against Fin.mk 44 _. -/
theorem RLI434U8.fin_300 (v : Fin 256) (h : v ≤ ⟨44, by decide⟩) : v ≤ Fin.ofNat 256 300 := h

/- An operand at the ceiling and just over it, with a small value: (65536 : UInt8) is 65536 % 2 ^ 8 = 0, and
   (65537 : UInt8) is 1. -/
theorem RLI434U8.le_65536 (v : UInt8) (h : v ≤ UInt8.ofNatLT 0 (by decide)) : v ≤ (65536 : UInt8) := h

theorem RLI434U8.le_65537 (v : UInt8) (h : v ≤ UInt8.ofNatLT 1 (by decide)) : v ≤ (65537 : UInt8) := h
