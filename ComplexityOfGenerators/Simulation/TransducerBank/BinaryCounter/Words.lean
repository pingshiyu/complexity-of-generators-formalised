import ComplexityOfGenerators.Foundations.FixedBitBlocks

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter

def increment : List Bool → List Bool
  | [] => [true]
  | false::rest => true::rest
  | true::rest => false::increment rest

/-- No redundant high zero digit. The least significant digit is first. -/
def Canonical : List Bool → Prop
  | [] => True
  | first::rest => (rest=[] ∧ first=true) ∨ (rest≠[] ∧ Canonical rest)

theorem canonical_tail {first : Bool} {rest : List Bool} (canonical : Canonical (first::rest)) : Canonical rest := by
  cases rest with
  | nil => trivial
  | cons next rest => exact canonical.resolve_left (by simp) |>.2

theorem canonical_cons {first : Bool} {rest : List Bool} (nonempty : rest≠[]) :
    Canonical (first::rest) ↔ Canonical rest := by
  simp [Canonical,nonempty]

theorem increment_nonempty (bits : List Bool) : increment bits≠[] := by
  cases bits with
  | nil => simp [increment]
  | cons first rest => cases first <;> simp [increment]

theorem increment_canonical (bits : List Bool) (canonical : Canonical bits) : Canonical (increment bits) := by
  induction bits with
  | nil => simp [increment,Canonical]
  | cons first rest ih =>
      cases first with
      | false =>
          cases rest with
          | nil => simp [increment,Canonical]
          | cons next tail =>
              change Canonical (true::next::tail)
              exact (canonical_cons (by simp)).mpr (canonical_tail canonical)
      | true =>
          rw [increment,canonical_cons (increment_nonempty rest)]
          exact ih (canonical_tail canonical)

theorem increment_value (bits : List Bool) :
    FixedBitBlocks.decode (increment bits)=FixedBitBlocks.decode bits+1 := by
  induction bits with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [increment,FixedBitBlocks.decode,ih] <;> omega

theorem canonical_value_positive (bits : List Bool) (canonical : Canonical bits) (nonempty : bits≠[]) :
    0<FixedBitBlocks.decode bits := by
  induction bits with
  | nil => contradiction
  | cons first rest ih =>
      cases rest with
      | nil =>
          have same : first=true := by simpa [Canonical] using canonical
          simp [same,FixedBitBlocks.decode]
      | cons next tail =>
          have positive := ih (canonical_tail canonical) (by simp)
          change 0<first.toNat+2*FixedBitBlocks.decode (next::tail)
          omega

/-- A numerical upper bound bounds the number of physical counter digits. -/
theorem canonical_length_bound (bits : List Bool) (canonical : Canonical bits) (width : ℕ)
    (small : FixedBitBlocks.decode bits<2^width) : bits.length≤width := by
  induction bits generalizing width with
  | nil => simp
  | cons first rest ih =>
      have tailCanonical := canonical_tail canonical
      cases rest with
      | nil =>
          have same : first=true := by simpa [Canonical] using canonical
          cases width with
          | zero => simp [same,FixedBitBlocks.decode] at small
          | succ width => simp
      | cons next tail =>
          have positive := canonical_value_positive (next::tail) tailCanonical (by simp)
          cases width with
          | zero =>
              change first.toNat+2*FixedBitBlocks.decode (next::tail)<1 at small
              omega
          | succ width =>
              have tailSmall : FixedBitBlocks.decode (next::tail)<2^width := by
                change first.toNat+2*FixedBitBlocks.decode (next::tail)<2^(width+1) at small
                rw [Nat.pow_succ] at small
                omega
              have length := ih tailCanonical width tailSmall
              simpa only [List.length_cons,Nat.add_le_add_iff_right] using Nat.add_le_add_right length 1

theorem iterate_canonical (count : ℕ) : Canonical (increment^[count] []) := by
  induction count with
  | zero => trivial
  | succ count ih => rw [Function.iterate_succ_apply']; exact increment_canonical _ ih

theorem iterate_value (count : ℕ) : FixedBitBlocks.decode (increment^[count] [])=count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply',increment_value,ih]

theorem iterate_length (count bound : ℕ) (small : count≤bound) :
    (increment^[count] []).length≤Nat.clog 2 (bound+1) := by
  apply canonical_length_bound _ (iterate_canonical count)
  rw [iterate_value]
  have power := Nat.le_pow_clog (by decide : 1<2) (bound+1)
  omega

theorem canonical_length_eq (bits : List Bool) (canonical : Canonical bits) :
    bits.length=Nat.clog 2 (FixedBitBlocks.decode bits+1) := by
  apply Nat.le_antisymm
  · apply canonical_length_bound bits canonical
    have power := Nat.le_pow_clog (by decide : 1<2) (FixedBitBlocks.decode bits+1)
    omega
  · apply Nat.clog_le_of_le_pow
    have bound := FixedBitBlocks.decode_bound bits
    omega

theorem iterate_length_eq (count : ℕ) : (increment^[count] []).length=Nat.clog 2 (count+1) := by
  simpa only [iterate_value] using canonical_length_eq (increment^[count] []) (iterate_canonical count)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter
