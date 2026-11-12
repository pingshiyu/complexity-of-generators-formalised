import ComplexityOfGenerators.Examples.SATNative.SubstitutionLoopBounds
import ComplexityOfGenerators.Examples.SATNative.SubstitutionHeaderBounds
import ComplexityOfGenerators.Examples.SATNative.SubstitutionReady

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] NativeParser.header NativeParser.bodySetup emitHeader substitutionRoutine
  bodyTransform prepareStream tailSetup selectLabel checkedStream

theorem prepareStream_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound (budget + 1) ((prepareStream (O := O)).eval s) := by
  rw [prepareStream_eval]
  exact NativeParser.bodySetup_bound _ _ (NativeParser.header_bound s budget sizes)

theorem prepareStream_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (prepareStream (O := O)).cost s ≤ 120 * (budget + 2) := by
  have first := NativeParser.header_cost (O := O) s budget sizes
  have after := NativeParser.header_bound (O := O) s budget sizes
  have second := NativeParser.bodySetup_cost (O := O) _ (budget + 1) after
  unfold prepareStream
  change (NativeParser.header (O := O)).cost s + 1 +
    (NativeParser.bodySetup (O := O)).cost ((NativeParser.header (O := O)).eval s) ≤ _
  omega

theorem tailSetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((tailSetup (O := O)).eval s) := by
  intro j
  rw [tailSetup_eval]
  by_cases scratch : j = 9 <;> by_cases tail : j = 22 <;>
    simp [scratch, tail, List.length_tail] <;> first | exact sizes _ | have := sizes 3; omega

theorem tailSetup_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (tailSetup (O := O)).cost s ≤ 20 * budget + 5 := by
  have source := sizes 3
  have copy := sizes 22
  have scratch := sizes 9
  simp only [tailSetup, Routine.seq, Routine.assign_cost, Routine.ofLocal, Local.pop, Local.ticks]
  omega

noncomputable def bodyBudget (arguments : ℕ) : ℕ :=
  200 * (arguments + 2) + 1 + arguments * ((NativeBody.stepConstant + 304) * ((arguments + 2)^2 + 1))

theorem bodyTransform_resources {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (arguments : ℕ) (sizes : stackBound (arguments + 1) s)
    (cap : capacity ≤ arguments) (activeBound : active ≤ capacity) (clock : (s 16).length ≤ arguments) :
    stackBound ((arguments + 2)^2) ((bodyTransform (O := O) bit).eval s) ∧
      (bodyTransform (O := O) bit).cost s ≤ bodyBudget arguments := by
  let prepared := (emitHeader (O := O)).eval s
  have within : (s 10).length - 1 ≤ (s 4).length := by
    rw [represented.2.2.1, represented.2.1]
    simp only [List.length_replicate]
    omega
  have firstBound := emitHeader_bound (O := O) s (arguments + 1) sizes within
  have firstCost := emitHeader_cost (O := O) s (arguments + 1) sizes
  have preparedRep := emitHeader_parserFrame (O := O) capacity active state s represented
  have sameClock : prepared 16 = s 16 := emitHeader_frame (O := O) s 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have actualClock : (prepared 16).length ≤ arguments := by rw [sameClock]; exact clock
  have fits : 2 * (arguments + 1) + 2 + (prepared 16).length * (capacity + 1) ≤ (arguments + 2)^2 := by
    have growth := Nat.mul_le_mul actualClock (Nat.add_le_add_right cap 1)
    nlinarith
  have loopBound := substitutionRoutine_growing_bound (O := O) bit capacity active state prepared preparedRep
    (2 * (arguments + 1) + 2) (by omega) firstBound (by omega) (by omega)
  have loopCost := substitutionRoutine_cost_ceiling (O := O) bit capacity active state prepared preparedRep
    (2 * (arguments + 1) + 2) (by omega) firstBound (by omega) (by omega) ((arguments + 2)^2) fits
  refine ⟨?_, ?_⟩
  · rw [bodyTransform_eval]
    intro j
    exact (loopBound j).trans fits
  · have loopCost' : (substitutionRoutine (O := O) bit).cost prepared ≤
        arguments * ((NativeBody.stepConstant + 304) * ((arguments + 2)^2 + 1)) :=
      loopCost.trans (Nat.mul_le_mul_right _ actualClock)
    unfold bodyTransform
    change (emitHeader (O := O)).cost s + 1 + (substitutionRoutine (O := O) bit).cost prepared ≤ _
    unfold bodyBudget
    omega

noncomputable def checkBudget (arguments : ℕ) : ℕ :=
  20 * (arguments + 2) + bodyBudget arguments + 3 * (arguments + 1) + 10

theorem checkLabel_resources {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (arguments : ℕ) (sizes : stackBound (arguments + 1) s)
    (cap : capacity ≤ arguments) (activeBound : active ≤ capacity) (clock : (s 16).length ≤ arguments) :
    stackBound ((arguments + 2)^2) ((checkLabel (O := O) bit).eval s) ∧
      (checkLabel (O := O) bit).cost s ≤ checkBudget arguments := by
  let prepared := (tailSetup (O := O)).eval s
  have preparedBound := tailSetup_bound (O := O) s (arguments + 1) sizes
  have preparedRep := tailSetup_represents (O := O) capacity active state s represented
  have sameClock : prepared 16 = s 16 := by simp [prepared, tailSetup_eval]
  have actualClock : (prepared 16).length ≤ arguments := by rw [sameClock]; exact clock
  have transform := bodyTransform_resources (O := O) bit capacity active state prepared preparedRep arguments preparedBound cap activeBound actualClock
  have prefixCost := tailSetup_cost (O := O) s (arguments + 1) sizes
  have flagBound := preparedBound 6
  change (prepared 6).length ≤ arguments + 1 at flagBound
  change (stackBound ((arguments + 2)^2)
    ((Routine.branch 22 fun tail => if tail.isSome then Routine.clear 6 else bodyTransform bit).eval prepared)) ∧ _
  by_cases present : (prepared 22).head?.isSome
  · have nonempty : prepared 22 ≠ [] := by intro empty; simp [empty] at present
    refine ⟨?_, ?_⟩
    · intro j
      have size : (prepared j).length ≤ arguments + 1 := preparedBound j
      by_cases flag : j = 6 <;> simp [Routine.branch, nonempty, Routine.clear, flag] <;> nlinarith
    · unfold checkLabel
      change (tailSetup (O := O)).cost s + 1 +
        (Routine.branch 22 fun tail => if tail.isSome then Routine.clear 6 else bodyTransform bit).cost prepared ≤ _
      simp only [Routine.branch, present, ite_true, Routine.clear]
      unfold checkBudget
      omega
  · have empty : prepared 22 = [] := by
      cases word : prepared 22 with
      | nil => rfl
      | cons head tail => simp [word] at present
    refine ⟨?_, ?_⟩
    · simpa [Routine.branch, empty] using transform.1
    · unfold checkLabel
      change (tailSetup (O := O)).cost s + 1 +
        (Routine.branch 22 fun tail => if tail.isSome then Routine.clear 6 else bodyTransform bit).cost prepared ≤ _
      simp only [Routine.branch, present, Bool.false_eq_true, ite_false]
      unfold checkBudget
      omega

noncomputable def selectBudget (arguments : ℕ) : ℕ :=
  checkBudget arguments + bodyBudget arguments + 3 * (arguments + 1) + 5

theorem selectLabel_resources {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (arguments : ℕ) (sizes : stackBound (arguments + 1) s)
    (cap : capacity ≤ arguments) (activeBound : active ≤ capacity) (clock : (s 16).length ≤ arguments) :
    stackBound ((arguments + 2)^2) ((selectLabel (O := O)).eval s) ∧
      (selectLabel (O := O)).cost s ≤ selectBudget arguments := by
  have no := checkLabel_resources (O := O) false capacity active state s represented arguments sizes cap activeBound clock
  have yes := checkLabel_resources (O := O) true capacity active state s represented arguments sizes cap activeBound clock
  have base := bodyTransform_resources (O := O) false capacity active state s represented arguments sizes cap activeBound clock
  have countReg := represented.2.2.1
  have clearBound : stackBound ((arguments + 2)^2) ((Routine.clear (O := O) 6).eval s) := by
    intro j
    by_cases flag : j = 6 <;> simp [Routine.clear, flag] <;> have := sizes j; nlinarith
  have clearCost : (Routine.clear (O := O) 6).cost s ≤ 3 * (arguments + 1) := by
    have := sizes 6
    simp only [Routine.clear]
    omega
  cases active with
  | zero =>
    cases label : (s 3).head? <;>
      simp only [selectLabel, Routine.branch, countReg, List.replicate_zero, List.head?_nil,
        Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ite_false, ite_true, label]
    · exact ⟨base.1, by unfold selectBudget; omega⟩
    · exact ⟨clearBound, by unfold selectBudget; omega⟩
  | succ active =>
    cases label : (s 3).head? with
    | none =>
      simp only [selectLabel, Routine.branch, countReg, List.replicate_succ, List.head?_cons,
        Option.isSome_some, ite_true, label]
      exact ⟨clearBound, by unfold selectBudget; omega⟩
    | some symbol =>
      cases symbol <;>
        simp only [selectLabel, Routine.branch, countReg, List.replicate_succ, List.head?_cons,
          Option.isSome_some, ite_true, label]
      all_goals first
        | exact ⟨no.1, by unfold selectBudget; omega⟩
        | exact ⟨yes.1, by unfold selectBudget; omega⟩
        | exact ⟨clearBound, by unfold selectBudget; omega⟩

noncomputable def checkedStreamBudget (arguments : ℕ) : ℕ := 120 * (arguments + 2) + 1 + selectBudget arguments

noncomputable def checkedStreamTime : PolynomialBound := PolynomialBound.ofPolynomial
  (2 * Polynomial.X * Polynomial.C (NativeBody.stepConstant + 304) * ((Polynomial.X + 2)^2 + 1) +
    540 * (Polynomial.X + 2) + 6 * (Polynomial.X + 1) + 18)

theorem checkedStreamBudget_le (arguments : ℕ) : checkedStreamBudget arguments ≤ checkedStreamTime arguments := by
  apply (PolynomialBound.eval_le_ofPolynomial _ arguments).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  unfold checkedStreamBudget selectBudget checkBudget bodyBudget
  nlinarith

theorem checkedStream_resources {O : Type} (s : Store) (arguments : ℕ) (sizes : stackBound arguments s) :
    stackBound ((arguments + 2)^2) ((checkedStream (O := O)).eval s) ∧
      (checkedStream (O := O)).cost s ≤ checkedStreamBudget arguments := by
  let prepared := (prepareStream (O := O)).eval s
  have preparedBound := prepareStream_bound (O := O) s arguments sizes
  have properties := prepareStream_properties (O := O) s
  dsimp only at properties
  have parsedSizes := NativeHeader.parsedState_bounds (s 2)
  have capacitySize := readOnes_lengths (s 2)
  have inputSize := sizes 2
  have cap : (readOnes (s 2)).1 ≤ arguments := by omega
  have activeBound : (NativeHeader.parsedState (s 2)).count ≤ (readOnes (s 2)).1 := parsedSizes.1
  have clock : (prepared 16).length ≤ arguments := by rw [properties.2.1]; omega
  have selected := selectLabel_resources (O := O) _ _ _ prepared properties.1 arguments preparedBound cap activeBound clock
  have prefixCost := prepareStream_cost (O := O) s arguments sizes
  refine ⟨?_, ?_⟩
  · rw [checkedStream_eval]
    exact selected.1
  · unfold checkedStream
    change (prepareStream (O := O)).cost s + 1 + (selectLabel (O := O)).cost prepared ≤ _
    unfold checkedStreamBudget
    omega

theorem checkedStream_cost {O : Type} (s : Store) (arguments : ℕ) (sizes : stackBound arguments s) :
    (checkedStream (O := O)).cost s ≤ checkedStreamTime arguments :=
  (checkedStream_resources s arguments sizes).2.trans (checkedStreamBudget_le arguments)

theorem checkedStream_bound {O : Type} (s : Store) (arguments : ℕ) (sizes : stackBound arguments s) :
    stackBound ((arguments + 2)^2) ((checkedStream (O := O)).eval s) :=
  (checkedStream_resources s arguments sizes).1

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
