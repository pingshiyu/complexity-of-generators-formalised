import ComplexityOfGenerators.Examples.SATNative.InverseNative.Iteration

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeBody
set_option backward.isDefEq.respectTransparency false

theorem counted_empty {O : Type} (bit : Bool) (capacity active : ℕ) (inside seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨[], inside, seen, enabled⟩ s) :
    let output := (countedStep (O := O) bit).eval s
    Represents capacity active ⟨[], inside, seen, enabled⟩ output ∧ output 31 = s 31 ∧ output 21 = s 21 := by
  have word : s 2 = [] := represented.1
  have output : (countedStep (O := O) bit).eval s = Function.update s 16 (s 16).tail := by
    simp [countedStep, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop,
      inverseStep, Routine.branch, word, Routine.skip, Local.eval]
  rw [output]
  exact ⟨NativeBody.popped_represents capacity active _ s represented, by simp, by simp⟩

theorem iterate_empty {O : Type} (bit : Bool) (capacity active count : ℕ) (inside seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨[], inside, seen, enabled⟩ s) :
    let output := (countedStep (O := O) bit).eval^[count] s
    Represents capacity active ⟨[], inside, seen, enabled⟩ output ∧ output 31 = s 31 ∧ output 21 = s 21 := by
  induction count generalizing s with
  | zero => exact ⟨represented, rfl, rfl⟩
  | succ count ih =>
    have one := counted_empty (O := O) bit capacity active inside seen enabled s represented
    have rest := ih _ one.1
    rw [Function.iterate_succ_apply]
    exact ⟨rest.1, rest.2.1.trans one.2.1, rest.2.2.trans one.2.2⟩

theorem inverseRoutine_formula {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨formula.bodyWord capacity, false, false, enabled⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (inverseRoutine (O := O) bit).eval s
    Represents capacity active ⟨[], false, false, enabled⟩ output ∧
      output 31 = (choices.drop formula.occurrences).map bitSymbol ∧
      output 21 = ((formula.lift active bit (choiceRows formula choices)).bodyWord capacity).reverse ++ s 21 := by
  have initial : Represents capacity active ⟨formula.bodyWord capacity ++ [], false, false, enabled⟩ s := by simpa using represented
  have first := iterate_formula (O := O) bit bound formula valid [] enabled s initial choices mask
  let middle := (countedStep (O := O) bit).eval^[NativeBody.tokenCount formula] s
  have rest := iterate_empty (O := O) bit capacity active ((s 16).length - NativeBody.tokenCount formula)
    false false enabled middle first.1
  change Represents capacity active _ ((countedStep (O := O) bit).eval^[(s 16).length] s) ∧
    ((countedStep (O := O) bit).eval^[(s 16).length] s) 31 = _ ∧
    ((countedStep (O := O) bit).eval^[(s 16).length] s) 21 = _
  rw [show (s 16).length = ((s 16).length - NativeBody.tokenCount formula) + NativeBody.tokenCount formula by omega,
    Function.iterate_add_apply]
  exact ⟨rest.1, rest.2.1.trans first.2.1, rest.2.2.trans first.2.2⟩

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
