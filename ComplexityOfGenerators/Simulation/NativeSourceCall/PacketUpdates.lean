import ComplexityOfGenerators.Simulation.NativeSourceCall.Memory

/-! Pointwise invariants for overlap-safe translation of the index packet.
The untouched suffix remains readable while a finite carry moves its prefix.
Only index marks move; every other alphabet track stays at its old coordinate. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall

/-- After the first cell was cleared, `count` old cells have been copied one
position to the right. The next old mark is held in finite control. -/
def rightBlock (length head : ℕ) (anchor : ℤ) (count : ℕ) (position : ℤ) : Option IndexMark :=
  if position=anchor then none
  else if anchor+1≤position ∧ position≤anchor+count then packet length head anchor (position-1)
  else packet length head anchor position

theorem rightBlock_zero (length head : ℕ) (anchor : ℤ) :
    rightBlock length head anchor 0 = Function.update (packet length head anchor) anchor none := by
  funext position
  by_cases same : position=anchor
  · simp [rightBlock, same]
  · have outside : ¬(anchor+1≤position ∧ position≤anchor+(0 : ℕ)) := by omega
    simp only [rightBlock, same, outside, Function.update_of_ne same, ↓reduceIte]

theorem rightBlock_current (length head count : ℕ) (anchor : ℤ) :
    rightBlock length head anchor count (anchor+count+1) = packet length head anchor (anchor+count+1) := by
  simp [rightBlock, show anchor+count+1 ≠ anchor by omega, show ¬anchor+count+1≤anchor+count by omega]

theorem rightBlock_step (length head count : ℕ) (anchor : ℤ) :
    Function.update (rightBlock length head anchor count) (anchor+count+1)
      (packet length head anchor (anchor+count)) = rightBlock length head anchor (count+1) := by
  funext position
  by_cases same : position=anchor+count+1
  · subst position
    rw [Function.update_self]
    have outside : ¬anchor+(count : ℤ)+1=anchor := by omega
    have inside : anchor+1≤anchor+(count : ℤ)+1 ∧ anchor+(count : ℤ)+1≤anchor+(count+1 : ℕ) := by omega
    simp only [rightBlock, outside, inside, ↓reduceIte]
    congr 1
    omega
  · rw [Function.update_of_ne same]
    unfold rightBlock
    have interval : (anchor+1≤position ∧ position≤anchor+count) ↔
        (anchor+1≤position ∧ position≤anchor+(count+1 : ℕ)) := by omega
    simp only [← interval]

theorem rightBlock_finish (length head : ℕ) (anchor : ℤ) :
    Function.update (rightBlock length head anchor length) (anchor+length+1)
      (packet length head anchor (anchor+length)) = packet length head (anchor+1) := by
  rw [rightBlock_step]
  funext position
  simp only [rightBlock, Nat.cast_add, Nat.cast_one]
  by_cases first : position=anchor
  · subst position
    simp [packet]
  · by_cases shifted : anchor+1≤position ∧ position≤anchor+(length : ℤ)+1
    · rw [if_neg first, if_pos (by omega)]
      exact (packet_shift length head anchor position 1).symm
    · have original : packet length head anchor position = none := by
        unfold packet
        split_ifs with inside
        · exfalso
          omega
        · rfl
      have moved : packet length head (anchor+1) position = none := by
        unfold packet
        split_ifs with inside
        · exfalso
          omega
        · rfl
      rw [if_neg first, if_neg (by omega), original, moved]

/-- The symmetric carry copies from the right endpoint towards the left. -/
def leftBlock (length head : ℕ) (anchor : ℤ) (count : ℕ) (position : ℤ) : Option IndexMark :=
  if position=anchor+length then none
  else if anchor+length-count≤position ∧ position<anchor+length then packet length head anchor (position+1)
  else packet length head anchor position

theorem leftBlock_zero (length head : ℕ) (anchor : ℤ) :
    leftBlock length head anchor 0 = Function.update (packet length head anchor) (anchor+length) none := by
  funext position
  by_cases same : position=anchor+length
  · simp [leftBlock, same]
  · have outside : ¬(anchor+length-(0 : ℕ)≤position ∧ position<anchor+length) := by omega
    simp only [leftBlock, same, outside, Function.update_of_ne same, ↓reduceIte]

theorem leftBlock_current (length head count : ℕ) (anchor : ℤ) :
    leftBlock length head anchor count (anchor+length-count-1) =
      packet length head anchor (anchor+length-count-1) := by
  simp [leftBlock, show anchor+length-count-1 ≠ anchor+length by omega,
    show ¬anchor+length-count≤anchor+length-count-1 by omega]

theorem leftBlock_step (length head count : ℕ) (anchor : ℤ) :
    Function.update (leftBlock length head anchor count) (anchor+length-count-1)
      (packet length head anchor (anchor+length-count)) = leftBlock length head anchor (count+1) := by
  funext position
  by_cases same : position=anchor+length-count-1
  · subst position
    rw [Function.update_self]
    have outside : ¬anchor+(length : ℤ)-count-1=anchor+length := by omega
    have inside : anchor+length-(count+1 : ℕ)≤anchor+(length : ℤ)-count-1 ∧
        anchor+(length : ℤ)-count-1<anchor+length := by omega
    simp only [leftBlock, outside, inside, ↓reduceIte]
    congr 1
    omega
  · rw [Function.update_of_ne same]
    unfold leftBlock
    have interval : (anchor+length-count≤position ∧ position<anchor+length) ↔
        (anchor+length-(count+1 : ℕ)≤position ∧ position<anchor+length) := by omega
    simp only [← interval]

theorem leftBlock_finish (length head : ℕ) (anchor : ℤ) :
    Function.update (leftBlock length head anchor length) (anchor-1)
      (packet length head anchor anchor) = packet length head (anchor-1) := by
  have finish := leftBlock_step length head length anchor
  have point : anchor+(length : ℤ)-length-1=anchor-1 := by omega
  have source : anchor+(length : ℤ)-length=anchor := by omega
  rw [point, source] at finish
  rw [finish]
  funext position
  simp only [leftBlock, Nat.cast_add, Nat.cast_one]
  by_cases last : position=anchor+length
  · subst position
    simp [packet]
  · by_cases shifted : anchor+(length : ℤ)-((length : ℤ)+1)≤position ∧ position<anchor+length
    · rw [if_neg last, if_pos (by omega)]
      have translated := packet_shift length head anchor position (-1)
      simpa [sub_eq_add_neg] using translated.symm
    · have original : packet length head anchor position = none := by
        unfold packet
        split_ifs with inside
        · exfalso
          omega
        · rfl
      have moved : packet length head (anchor-1) position = none := by
        unfold packet
        split_ifs with inside
        · exfalso
          omega
        · rfl
      rw [if_neg last, if_neg (by omega), original, moved]

end ComplexityOfGenerators.Simulation.NativeSourceCall
