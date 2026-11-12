import ComplexityOfGenerators.Examples.SATNative.SubstitutionIteration

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem substitutionRoutine_represents {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active ((NativeBody.step capacity active)^[(s 16).length] state)
      ((substitutionRoutine (O := O) bit).eval s) := by
  have one (state : State) (s : Store) (represented : Represents capacity active state s) :
      Represents capacity active (NativeBody.step capacity active state) ((countedStep (O := O) bit).eval s) := by
    exact substitutionStep_represents (O := O) bit capacity active state _
      (NativeBody.popped_represents capacity active state s represented)
  have iter (count : ℕ) : ∀ state s, Represents capacity active state s →
      Represents capacity active ((NativeBody.step capacity active)^[count] state)
        ((countedStep (O := O) bit).eval^[count] s) := by
    induction count with
    | zero => intro state s h; exact h
    | succ count ih =>
      intro state s h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _ (one state s h)
  exact iter _ state s represented

theorem counted_empty {O : Type} (bit : Bool) (capacity active : ℕ) (inside seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨[], inside, seen, enabled⟩ s) :
    let output := (countedStep (O := O) bit).eval s
    Represents capacity active ⟨[], inside, seen, enabled⟩ output ∧ output 21 = s 21 := by
  have word : s 2 = [] := represented.1
  have output : (countedStep (O := O) bit).eval s = Function.update s 16 (s 16).tail := by
    simp [countedStep, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop,
      substitutionStep, Routine.branch, word, Routine.skip, Local.eval]
  rw [output]
  exact ⟨NativeBody.popped_represents capacity active _ s represented, by simp⟩

theorem iterate_empty {O : Type} (bit : Bool) (capacity active count : ℕ) (inside seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨[], inside, seen, enabled⟩ s) :
    let output := (countedStep (O := O) bit).eval^[count] s
    Represents capacity active ⟨[], inside, seen, enabled⟩ output ∧ output 21 = s 21 := by
  induction count generalizing s with
  | zero => exact ⟨represented, rfl⟩
  | succ count ih =>
    have one := counted_empty (O := O) bit capacity active inside seen enabled s represented
    have rest := ih _ one.1
    rw [Function.iterate_succ_apply]
    exact ⟨rest.1, rest.2.trans one.2⟩

/-- The full native streaming loop reconstructs semantic substitution on all
well-formed formulas. Extra clock iterations see an empty source and preserve
the complete reversed output buffer. -/
theorem substitutionRoutine_formula {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨formula.bodyWord capacity, false, false, enabled⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length) :
    let output := (substitutionRoutine (O := O) bit).eval s
    Represents capacity active ⟨[], false, false, enabled⟩ output ∧
      output 21 = ((formula.substitute active bit).bodyWord capacity).reverse ++ s 21 := by
  have initial : Represents capacity active ⟨formula.bodyWord capacity ++ [], false, false, enabled⟩ s := by simpa using represented
  have first := iterate_formula (O := O) bit bound formula valid [] enabled s initial
  let middle := (countedStep (O := O) bit).eval^[NativeBody.tokenCount formula] s
  have rest := iterate_empty (O := O) bit capacity active ((s 16).length - NativeBody.tokenCount formula)
    false false enabled middle first.1
  change Represents capacity active _ ((countedStep (O := O) bit).eval^[(s 16).length] s) ∧
    ((countedStep (O := O) bit).eval^[(s 16).length] s) 21 = _
  rw [show (s 16).length = ((s 16).length - NativeBody.tokenCount formula) + NativeBody.tokenCount formula by omega,
    Function.iterate_add_apply]
  exact ⟨rest.1, rest.2.trans first.2⟩

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
