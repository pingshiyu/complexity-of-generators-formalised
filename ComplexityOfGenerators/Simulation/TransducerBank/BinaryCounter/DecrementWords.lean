import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Words

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter

def decrement : List Bool → List Bool
  | [] => []
  | true::rest => if rest=[] then [] else false::rest
  | false::rest => true::decrement rest

theorem decrement_length (bits : List Bool) : (decrement bits).length≤bits.length := by
  induction bits with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | false => simpa only [decrement,List.length_cons,Nat.add_le_add_iff_right] using ih
      | true => simp only [decrement]; split_ifs <;> simp

theorem decrement_canonical (bits : List Bool) (canonical : Canonical bits) : Canonical (decrement bits) := by
  induction bits with
  | nil => trivial
  | cons first rest ih =>
      have tailCanonical := canonical_tail canonical
      cases first with
      | true =>
          by_cases empty : rest=[]
          · simp [decrement,empty,Canonical]
          · simpa [decrement,empty,canonical_cons empty] using tailCanonical
      | false =>
          have tail := ih tailCanonical
          by_cases empty : decrement rest=[]
          · simp [decrement,empty,Canonical]
          · simpa [decrement,canonical_cons empty] using tail

theorem decrement_value (bits : List Bool) (canonical : Canonical bits) :
    FixedBitBlocks.decode (decrement bits)=FixedBitBlocks.decode bits-1 := by
  induction bits with
  | nil => rfl
  | cons first rest ih =>
      have tailCanonical := canonical_tail canonical
      cases first with
      | true =>
          by_cases empty : rest=[]
          · simp [decrement,empty,FixedBitBlocks.decode]
          · simp [decrement,empty,FixedBitBlocks.decode]
      | false =>
          have nonempty : rest≠[] := by
            intro empty
            simp [Canonical,empty] at canonical
          have positive := canonical_value_positive rest tailCanonical nonempty
          have value := ih tailCanonical
          simp only [decrement,FixedBitBlocks.decode,Bool.toNat_true,Bool.toNat_false,Nat.zero_add]
          omega

theorem decrement_increment (bits : List Bool) (canonical : Canonical bits) : decrement (increment bits)=bits := by
  induction bits with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | false =>
          have nonempty : rest≠[] := by
            intro empty
            simp [Canonical,empty] at canonical
          simp [increment,decrement,nonempty]
      | true => simp [increment,decrement,ih (canonical_tail canonical)]

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter
