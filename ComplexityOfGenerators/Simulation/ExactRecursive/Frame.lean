import ComplexityOfGenerators.Simulation.ExactRecursive.Components

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

private theorem outside_source (j : Fin 35) (large : 17 ≤ j.val) :
    ∀ i, j ≠ Source.bank sourceSlots i := by
  intro i equal
  have same := congrArg Fin.val equal
  change j.val = i.val at same
  omega

theorem counter_fixes (value : Fin 35)
    (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21)
    (p : PolynomialBound) (j : Fin 35) (hv : j ≠ value) (h19 : j ≠ 19) (h20 : j ≠ 20) (h21 : j ≠ 21) :
    (counter B V value different p).Fixes j := by
  intro s
  simp [counter, CounterRoutine.routine_eval, hv, h19, h20, h21]

theorem sourceTrial_fixes {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (f g b : Cell B V → Cell B V) (seed time : PolynomialBound)
    (j : Fin 35) (large : 22 ≤ j.val) : (sourceTrial B V M encode decode f g b seed time).Fixes j := by
  have counterFrame (p : PolynomialBound) (value : Fin 35)
      (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21) (small : value.val < 22) :
      (counter B V value different p).Fixes j := by
    intro s
    have neq : j ≠ value := by intro eq; subst j; omega
    have h19 : j ≠ 19 := by omega
    have h20 : j ≠ 20 := by omega
    have h21 : j ≠ 21 := by omega
    simp [counter, CounterRoutine.routine_eval, neq, h19, h20, h21]
  apply WordStack.Routine.Fixes.seq (counterFrame seed 18 (by decide) (by decide))
  apply WordStack.Routine.Fixes.seq
  · intro s
    have h18 : j ≠ 18 := by omega
    have h17 : j ≠ 17 := by omega
    have h14 : j ≠ 14 := by omega
    simp [Blocks.routine_eval (k := 35) 18 17 14 (by decide) (by decide) (by decide), h18, h17, h14]
  apply WordStack.Routine.Fixes.seq (counterFrame time 16 (by decide) (by decide))
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_push (O := α) 16 j (show Cell B V from .unit) (by omega))
  intro s
  rw [Source.call_frame M sourceSlots encode decode f g b s j (outside_source j (by omega)) (by
    change j ≠ (16 : Fin 35); omega)]
  have h14 : j ≠ (14 : Fin 35) := by omega
  have h15 : j ≠ (15 : Fin 35) := by omega
  change (if j = (14 : Fin 35) ∨ j = (15 : Fin 35) then [] else s j) = s j
  simp [h14, h15]

theorem flag_fixes (reg j : Fin 35) (value : Bool) (different : j ≠ reg) : (flag B V reg value).Fixes j := by
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_clear reg j different)
  cases value
  · exact WordStack.Routine.fixes_skip j
  · exact WordStack.Routine.fixes_push (O := α) reg j (show Cell B V from .unit) different

theorem coin_fixes (no yes : Controller B V) (j : Fin 35) (random : j ≠ 17)
    (hn : no.Fixes j) (hy : yes.Fixes j) : (coin B V no yes).Fixes j := by
  apply WordStack.Routine.Fixes.branch
  intro head
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_pop 17 j random)
  split <;> assumption

theorem takeOutput_fixes (dst : Fin 35) (different : (10 : Fin 35) ≠ dst) (map : Cell B V → Cell B V)
    (j : Fin 35) (output : j ≠ 10) (destination : j ≠ dst) : (takeOutput B V dst different map).Fixes j :=
  (WordStack.Routine.fixes_clear dst j destination).seq
    (WordStack.Routine.fixes_transfer 10 dst different map j output destination)

theorem offer_fixes (coin : Bool) (j : Fin 35) (h10 : j ≠ 10) (h25 : j ≠ 25)
    (h26 : j ≠ 26) (h27 : j ≠ 27) : (offer B V coin).Fixes j := by
  apply WordStack.Routine.Fixes.branch
  intro locked
  split
  · exact WordStack.Routine.fixes_skip j
  · apply WordStack.Routine.Fixes.branch
    intro label
    split
    · exact WordStack.Routine.fixes_skip j
    · apply WordStack.Routine.Fixes.branch
      intro status
      split
      · apply WordStack.Routine.Fixes.seq (takeOutput_fixes B V 25 (by decide) _ j h10 h25)
        apply WordStack.Routine.Fixes.seq (flag_fixes B V 27 j true h27)
        cases coin
        · exact WordStack.Routine.fixes_skip j
        · exact flag_fixes B V 26 j true h26
      · exact WordStack.Routine.fixes_skip j

theorem increment_fixes (first : α) (j : Fin 35) (h12 : j ≠ 12) (h24 : j ≠ 24) :
    (increment B V first).Fixes j := by
  intro s
  simp [increment, WordCounter.routine_eval, h12, h24]

theorem searchStep_fixes (first : α) (seed time : PolynomialBound) (j : Fin 35) (clock : j = 22 ∨ j = 23) :
    (searchStep B V first seed time).Fixes j := by
  have large : 22 ≤ j.val := by rcases clock with rfl | rfl <;> decide
  have h10 : j ≠ 10 := by omega
  have h12 : j ≠ 12 := by omega
  have h17 : j ≠ 17 := by omega
  have h24 : j ≠ 24 := by rcases clock with rfl | rfl <;> decide
  have h25 : j ≠ 25 := by rcases clock with rfl | rfl <;> decide
  have h26 : j ≠ 26 := by rcases clock with rfl | rfl <;> decide
  have h27 : j ≠ 27 := by rcases clock with rfl | rfl <;> decide
  exact (sourceTrial_fixes B V V _ _ _ _ _ seed time j large).seq
    ((coin_fixes B V _ _ j h17 (offer_fixes B V false j h10 h25 h26 h27)
      (offer_fixes B V true j h10 h25 h26 h27)).seq (increment_fixes B V first j h12 h24))

theorem searchStep_fixes_high (first : α) (seed time : PolynomialBound) (j : Fin 35) (large : 28 ≤ j.val) :
    (searchStep B V first seed time).Fixes j := by
  have h10 : j ≠ 10 := by omega
  have h12 : j ≠ 12 := by omega
  have h17 : j ≠ 17 := by omega
  have h24 : j ≠ 24 := by omega
  have h25 : j ≠ 25 := by omega
  have h26 : j ≠ 26 := by omega
  have h27 : j ≠ 27 := by omega
  exact (sourceTrial_fixes B V V _ _ _ _ _ seed time j (by omega)).seq
    ((coin_fixes B V _ _ j h17 (offer_fixes B V false j h10 h25 h26 h27)
      (offer_fixes B V true j h10 h25 h26 h27)).seq (increment_fixes B V first j h12 h24))

end ComplexityOfGenerators.Simulation.ExactRecursive
