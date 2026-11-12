import ComplexityOfGenerators.Simulation.StarPaths.ResourceBounds

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem fallback_held_bound (flags : List Bool) (n : ℕ) :
    (held (fallback flags n)).length ≤ 2*n := by
  cases value : fallback flags n with
  | none => simp [held]
  | some parts => exact valid_payload_bound flags n parts ((fallback_spec flags n).1 parts value)

theorem stageSetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((stageSetup (O := O)).eval s) budget ∧
      (stageSetup (O := O)).cost s ≤ 100*(budget+1) := by
  constructor
  · exact (((sizes.assign 4 5 12 (by decide) (by decide) (by decide) id).assign
      25 6 12 (by decide) (by decide) (by decide) id).assign
        1 2 12 (by decide) (by decide) (by decide) id).clearMany [3,10,11]
  · have a := sizes 5
    have b := sizes 4
    have c := sizes 12
    have d := sizes 6
    have e := sizes 25
    have f := sizes 2
    have g := sizes 1
    have h := sizes 3
    have i := sizes 10
    have j := sizes 11
    simp [stageSetup,WordStack.Routine.seq,WordStack.Routine.assign_cost,WordStack.Routine.assign_eval,
      WordStack.Routine.clearMany,WordStack.Routine.clear,WordStack.Routine.skip,
      WordStack.Routine.ofLocal,Local.ticks]
    omega

theorem appendEntry_bound {O : Type} (s : Store) (budget wordLimit : ℕ)
    (sizes : StoreBound s budget) (word : (s 10).length ≤ wordLimit) :
    StoreBound ((appendEntry (O := O)).eval s) (budget+wordLimit+1) ∧
      (appendEntry (O := O)).cost s ≤ 30*(budget+1) := by
  by_cases found : (s 11).head?.isSome = true
  · simp only [appendEntry,WordStack.Routine.branch,found,ite_true]
    constructor
    · simp only [WordStack.Routine.seq,WordStack.Routine.copy,WordStack.Routine.ofLocal,
        Local.eval_push,Function.update_self,Function.update_idem]
      change StoreBound (Function.update (Function.update s 12 []) 4 (Symbol.present::((s 10).map id++s 4))) _
      apply ((sizes.mono (by omega)).clear 12).update 4 _ ?_
      simp only [List.length_cons,List.length_append,List.length_map]
      have := sizes 4
      omega
    · have a := sizes 12
      have b := sizes 10
      simp [WordStack.Routine.seq,WordStack.Routine.copy,WordStack.Routine.ofLocal,Local.push,Local.ticks]
      omega
  · simp only [appendEntry,WordStack.Routine.branch,found,Bool.false_eq_true,ite_false]
    constructor
    · change StoreBound (Function.update s 4 (Symbol.absent::s 4)) _
      apply (sizes.mono (by omega)).update 4 _ ?_
      simp only [List.length_cons]
      have := sizes 4
      omega
    · simp [WordStack.Routine.ofLocal,Local.push,Local.ticks]
      omega

/-- Each DP stage grows a store budget by a quadratic additive amount; it
does not multiply the previous stage's workspace budget. -/
theorem outerBody_bound {O : Type} (flags : List Bool) (stage target : ℕ) (s : Store) (budget : ℕ)
    (positive : 1 ≤ budget) (sizes : StoreBound s budget) (represented : DPRep flags stage s)
    (inside : stage < target) :
    StoreBound ((outerBody (O := O)).eval s) (budget+(target+3)^2) ∧
      (outerBody (O := O)).cost s ≤ (1000*(target+3)^3)*(budget+1) := by
  let pushed := Function.update s 1 (Symbol.unit::s 1)
  let prepared := (stageSetup (O := O)).eval pushed
  let walked := (stageRoutine (O := O)).eval prepared
  have pushedBound : StoreBound pushed (budget+1) :=
    (sizes.mono (by omega)).update 1 _ (by simpa using Nat.add_le_add_right (sizes 1) 1)
  have setup := stageSetup_bound (O := O) pushed (budget+1) pushedBound
  have clock : (prepared 2).length = stage+1 := by
    rw [stageSetup_clock]
    simp [pushed,represented.1]
  have counter : (prepared 3).length = 0 := by
    simp [prepared,stageSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]
  have loop := stageRoutine_bound (O := O) prepared (budget+1) target (by omega) setup.1 (by omega)
  have loopUpper : budget+1+(prepared 2).length*(target+3) ≤ budget+1+target*(target+3) := by
    rw [clock]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have walkedBound : StoreBound walked (budget+1+target*(target+3)) := loop.1.mono loopUpper
  have next := outerBody_represents (O := O) flags stage s represented
  have finalWord : walked 10 = held (fallback flags (stage+1)) := by
    have word := next.2.2.2.1
    change (appendEntry (O := O)).eval walked 10 = _ at word
    rw [appendEntry_frame 10 (by decide) (by decide)] at word
    exact word
  have wordBound : (walked 10).length ≤ 2*target := by
    rw [finalWord]
    exact (fallback_held_bound flags (stage+1)).trans (Nat.mul_le_mul_left 2 (by omega))
  have appended := appendEntry_bound (O := O) walked (budget+1+target*(target+3)) (2*target) walkedBound wordBound
  constructor
  · exact appended.1.mono (by nlinarith)
  · have loopCost : (stageRoutine (O := O)).cost prepared ≤
        target*304*(budget+1+target*(target+3)+1) := by
      apply loop.2.trans
      exact Nat.mul_le_mul (Nat.mul_le_mul_right 304 (by omega)) (Nat.add_le_add_right loopUpper 1)
    have setupCost := setup.2
    have appendCost := appended.2
    change 1+1+((stageSetup (O := O)).cost pushed+1+
      ((stageRoutine (O := O)).cost prepared+1+(appendEntry (O := O)).cost walked)) ≤ _
    have ceiling : budget+1+target*(target+3)+1 ≤ budget+(target+3)^2+1 := by nlinarith
    have setupCeiling : budget+1+1 ≤ budget+(target+3)^2+1 := by nlinarith
    have preliminary : 1+1+((stageSetup (O := O)).cost pushed+1+
        ((stageRoutine (O := O)).cost prepared+1+(appendEntry (O := O)).cost walked)) ≤
        (target*304+150)*(budget+(target+3)^2+1) := by
      have hloop := loopCost.trans (Nat.mul_le_mul_left (target*304) ceiling)
      have hsetup := setupCost.trans (Nat.mul_le_mul_left 100 setupCeiling)
      have happend := appendCost.trans (Nat.mul_le_mul_left 30 ceiling)
      nlinarith
    have square : 2 ≤ (target+3)^2 := by nlinarith
    have factored : budget+(target+3)^2+1 ≤ (budget+1)*(target+3)^2 := by
      have lower := Nat.mul_le_mul_left budget square
      nlinarith
    calc
      _ ≤ (target*304+150)*(budget+(target+3)^2+1) := preliminary
      _ ≤ (1000*(target+3))*((budget+1)*(target+3)^2) :=
        Nat.mul_le_mul (by omega) factored
      _ = _ := by ring

end ComplexityOfGenerators.Simulation.StarPaths
