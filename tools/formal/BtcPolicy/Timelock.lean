import BtcPolicy.Req
/-! `CHN-4`'s default recovery timelock, executed rather than read: "On a default vault it MUST be
`older(4224679)`, which is the BIP68 time-based relative lock of `30375` units of 512 seconds with
type-flag bit 22 set (`30375 | (1 << 22)`), that is 180 days."

The consensus constants are unit conversions, not copies of a configured value; the default
operands are the ones the copies gate reads back out of `CHN-4`, `CHN-1`, `CHN-8` and `CHN-10`. -/

namespace BtcPolicy.Timelock

/-- BIP68: bit 22 selects a time-based lock; a unit is 512 seconds; the field is 16 bits. The
first two are figures `CHN-4` gives and the copies gate reads back. -/
@[req "CHN-4"] def typeFlagBit : Nat := 22
@[req "CHN-4"] def secondsPerUnit : Nat := 512
def secondsPerDay : Nat := 86400
def unitFieldWidth : Nat := 16

/-- `CHN-4`: a time-based relative lock of `units` encodes as `units | (1 << 22)`. -/
@[req "CHN-4"]
def bip68Time (units : Nat) : Nat := units ||| (1 <<< typeFlagBit)

/-- The default vault's operands. -/
@[req "CHN-4"] def defaultUnits : Nat := 30375
@[req "CHN-4"] def defaultNSequence : Nat := 4224679
@[req "CHN-4"] def defaultDays : Nat := 180

/-- The published `nSequence` follows from the published units and flag. -/
@[req "CHN-4"]
theorem nsequence_derived : bip68Time defaultUnits = defaultNSequence := by decide

/-- The published day count follows, and exactly — no remainder. -/
@[req "CHN-4"]
theorem days_derived :
    defaultUnits * secondsPerUnit / secondsPerDay = defaultDays ∧
    defaultUnits * secondsPerUnit % secondsPerDay = 0 := by decide

/-- "MUST refuse a value above the 65535-unit field": the default fits. -/
@[req "CHN-4"]
theorem units_fit : 0 < defaultUnits ∧ defaultUnits < 1 <<< unitFieldWidth := by decide

/-- Beyond the gate: the encoding is invertible on the whole field. For EVERY units value below
`2^16`, masking the encoded `nSequence` back to 16 bits recovers the units, and bit 22 reads
set — the parser rule "MUST require bit 22 set" as a property over the domain, not at one point. -/
@[req "CHN-4"]
theorem encode_roundtrip (units : Nat) (h : units < 1 <<< unitFieldWidth) :
    bip68Time units &&& 0xFFFF = units ∧ (bip68Time units).testBit typeFlagBit = true := by
  unfold bip68Time typeFlagBit unitFieldWidth at *
  constructor
  · have hlt : units < 2 ^ 16 := by simpa using h
    have h1 : units &&& 0xFFFF = units := by
      have := Nat.and_two_pow_sub_one_of_lt_two_pow hlt
      simpa using this
    rw [Nat.and_or_distrib_right]
    have h2 : (1 <<< 22) &&& 0xFFFF = 0 := by decide
    rw [h2, h1]; simp
  · simp [Nat.testBit_or]
    right; decide

/-- The trap `CHN-4` names: `older(30375)` without the flag is a HEIGHT lock. -/
@[req "CHN-4"]
theorem bare_units_are_not_the_lock : defaultUnits ≠ defaultNSequence := by decide

end BtcPolicy.Timelock
