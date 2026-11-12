import ComplexityOfGenerators.Simulation.NativeSourceCall.Memory

/-! Clearing and reinstalling the virtual index marker changes no packet
boundary, including clamped moves at either endpoint. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall

def headless (length : ℕ) (anchor position : ℤ) : Option IndexMark :=
  if anchor≤position ∧ position≤anchor+length then
    some ⟨decide (position=anchor), decide (position=anchor+length), false⟩ else none

theorem clear_head (length head : ℕ) (within : head≤length) (anchor : ℤ) :
    Function.update (packet length head anchor) (anchor+head)
      (some ⟨decide (head=0), decide (head=length), false⟩) = headless length anchor := by
  funext position
  by_cases same : position=anchor+head
  · subst position
    simp [headless, within]
  · rw [Function.update_of_ne same]
    simp only [packet, headless]
    split_ifs with inside
    · congr 2
      exact decide_eq_false same
    · rfl

theorem headless_at (length head : ℕ) (within : head≤length) (anchor : ℤ) :
    headless length anchor (anchor+head) = some ⟨decide (head=0), decide (head=length), false⟩ := by
  simp [headless, within]

theorem place_head (length head : ℕ) (within : head≤length) (anchor : ℤ) :
    Function.update (headless length anchor) (anchor+head)
      (some ⟨decide (head=0), decide (head=length), true⟩) = packet length head anchor := by
  funext position
  by_cases same : position=anchor+head
  · subst position
    simp [packet, within]
  · rw [Function.update_of_ne same]
    simp only [headless, packet]
    split_ifs with inside
    · congr 2
      exact (decide_eq_false same).symm
    · rfl

end ComplexityOfGenerators.Simulation.NativeSourceCall
