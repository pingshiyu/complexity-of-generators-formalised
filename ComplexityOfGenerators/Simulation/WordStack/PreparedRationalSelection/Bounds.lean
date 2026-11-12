import ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection.Basic
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection

set_option backward.isDefEq.respectTransparency false

variable {S O : Type}

theorem difference_bound (encode : Bool → S) (high subtractor destination : Fin 35)
    (highSafe : Safe high) (subtractorSafe : Safe subtractor) (small : destination.val < 2)
    (s : Store S) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((difference (O := O) encode high subtractor destination highSafe subtractorSafe small).eval s) budget := by
  rw [difference_eval]
  exact ((((sizes.clear 33).update destination _ (by
    simp only [List.length_replicate]
    exact (Nat.sub_le _ _).trans (sizes high))).clear 3).clear 4)

theorem assign_cost_le (src dst scratch : Fin 35)
    (sd : src ≠ dst) (st : src ≠ scratch) (dt : dst ≠ scratch)
    (f : S → S) (s : Store S) (budget : ℕ) (sizes : StoreBound s budget) :
    (Routine.assign (O := O) src dst scratch sd st dt f).cost s ≤ 20 * budget + 3 := by
  rw [Routine.assign_cost]
  have one := sizes src
  have two := sizes dst
  have three := sizes scratch
  omega

theorem difference_cost_le (encode : Bool → S) (high subtractor destination : Fin 35)
    (highSafe : Safe high) (subtractorSafe : Safe subtractor) (small : destination.val < 2)
    (s : Store S) (budget : ℕ) (sizes : StoreBound s budget) :
    (difference (O := O) encode high subtractor destination highSafe subtractorSafe small).cost s ≤
      50 * (budget + 1) := by
  have highDst : high ≠ destination := by intro h; have := highSafe.1; subst high; omega
  have subThree : subtractor ≠ 3 := by intro h; have := subtractorSafe.1; subst subtractor; omega
  have dstScratch : destination ≠ 33 := by intro h; subst destination; norm_num at small
  have threeDst : (3 : Fin 35) ≠ destination := by intro h; subst destination; norm_num at small
  let first : Routine S O 35 := Routine.assign high destination 33 highDst highSafe.2 dstScratch (fun _ => encode true)
  let second : Routine S O 35 := Routine.assign subtractor 3 33 subThree subtractorSafe.2 (by decide) (fun _ => encode true)
  let afterFirst := first.eval s
  let afterSecond := second.eval afterFirst
  have firstBound : StoreBound afterFirst budget := sizes.assign high destination 33 _ _ _ _
  have secondBound : StoreBound afterSecond budget := firstBound.assign subtractor 3 33 _ _ _ _
  have firstCost : first.cost s ≤ 20 * budget + 3 := assign_cost_le _ _ _ _ _ _ _ _ budget sizes
  have secondCost : second.cost afterFirst ≤ 20 * budget + 3 := assign_cost_le _ _ _ _ _ _ _ _ budget firstBound
  have clearCost : (Routine.clear (O := O) (4 : Fin 35)).cost afterSecond ≤ 3 * budget := by
    exact Nat.mul_le_mul_left 3 (secondBound 4)
  have drainCost := DrainPair.routine_cost (O := O) 3 destination 4 threeDst (by decide)
    ((Routine.clear (O := O) (4 : Fin 35)).eval afterSecond)
  have counterBound : (((Routine.clear (O := O) (4 : Fin 35)).eval afterSecond) 3).length ≤ budget :=
    (secondBound.clear 4) 3
  change first.cost s + 1 + (second.cost afterFirst + 1 +
    ((Routine.clear (O := O) (4 : Fin 35)).cost afterSecond + 1 +
      (DrainPair.routine (O := O) 3 destination 4 threeDst (by decide)).cost
        ((Routine.clear (O := O) (4 : Fin 35)).eval afterSecond))) ≤ _
  omega

theorem clearMany_bound (registers : List (Fin 35)) (s : Store S) (budget : ℕ)
    (sizes : StoreBound s budget) :
    StoreBound ((Routine.clearMany (O := O) registers).eval s) budget := by
  exact sizes.clearMany registers

theorem prepare_bound (encode : Bool → S) (decode : S → Bool) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepare (O := O) encode decode low high lowSafe highSafe).eval s) budget := by
  change StoreBound ((Routine.assign (O := O) 17 2 33 (by decide) (by decide) (by decide) _).eval
    ((difference (O := O) encode high 22 1 highSafe (by decide) (by decide)).eval
      ((difference (O := O) encode high low 0 highSafe lowSafe (by decide)).eval
        ((Routine.clearMany (O := O) bank).eval s)))) budget
  have initial := clearMany_bound (O := O) bank s budget sizes
  have left := difference_bound (O := O) encode high low 0 highSafe lowSafe (by decide) _ budget initial
  have right := difference_bound (O := O) encode high 22 1 highSafe (by decide) (by decide) _ budget left
  exact right.assign 17 2 33 (by decide) (by decide) (by decide) _

theorem prepare_cost_le (encode : Bool → S) (decode : S → Bool) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) (budget : ℕ) (sizes : StoreBound s budget) :
    (prepare (O := O) encode decode low high lowSafe highSafe).cost s ≤ 200 * (budget + 1) := by
  let first := (Routine.clearMany (S := S) (O := O) bank).eval s
  let second := (difference (O := O) encode high low 0 highSafe lowSafe (by decide)).eval first
  let third := (difference (O := O) encode high 22 1 highSafe (by decide) (by decide)).eval second
  have firstBound : StoreBound first budget := clearMany_bound bank s budget sizes
  have secondBound : StoreBound second budget := difference_bound _ _ _ _ _ _ _ first budget firstBound
  have thirdBound : StoreBound third budget := difference_bound _ _ _ _ _ _ _ second budget secondBound
  have one := Routine.clearMany_cost (O := O) bank s budget (fun j _ => sizes j)
  have two := difference_cost_le (O := O) encode high low 0 highSafe lowSafe (by decide) first budget firstBound
  have three := difference_cost_le (O := O) encode high 22 1 highSafe (by decide) (by decide) second budget secondBound
  have four := assign_cost_le (O := O) 17 2 33 (by decide) (by decide) (by decide)
    (fun symbol => encode (decode symbol)) third budget thirdBound
  have bankLength : bank.length = 16 := by simp [bank]
  rw [bankLength] at one
  change (Routine.clearMany (O := O) bank).cost s + 1 +
    ((difference (O := O) encode high low 0 highSafe lowSafe (by decide)).cost first + 1 +
      ((difference (O := O) encode high 22 1 highSafe (by decide) (by decide)).cost second + 1 +
        (Routine.assign (O := O) 17 2 33 (by decide) (by decide) (by decide) _).cost third)) ≤ _
  omega

theorem routine_owned_bound (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S)
    (positive : 0 < (s high).length - (s low).length)
    (ordered : (s high).length - (s 22).length ≤ (s high).length - (s low).length)
    (enough : Nat.clog 2 ((s high).length - (s low).length) ≤ (s 17).length) (j : Fin 16) :
    (((routine (O := O) encode decode retract low high lowSafe highSafe).eval s) (slots j)).length ≤
      20 * ((s high).length - (s low).length + (s 17).length + 1) := by
  rw [routine_owned, List.length_map]
  simpa only [input, List.length_map] using RationalSelection.selector_input_bound (O := O) ((s high).length - (s low).length)
    ((s high).length - (s 22).length) ((s 17).map decode) positive ordered
    (by simpa only [List.length_map] using enough) j

theorem routine_scratch (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) :
    ((routine (O := O) encode decode retract low high lowSafe highSafe).eval s) 33 = [] := by
  rw [routine_eval, finalStore, Memory.patchStore_outside]
  · simp [preparedStore]
  · intro j same
    have values := congrArg Fin.val same
    have := j.isLt
    simp [slots] at values
    omega

theorem routine_cost_le (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) (budget : ℕ) (sizes : StoreBound s budget)
    (positive : 0 < (s high).length - (s low).length)
    (ordered : (s high).length - (s 22).length ≤ (s high).length - (s low).length)
    (enough : Nat.clog 2 ((s high).length - (s low).length) ≤ (s 17).length) :
    (routine (O := O) encode decode retract low high lowSafe highSafe).cost s ≤ 100000 * (budget + 1)^2 := by
  have prep := prepare_cost_le (O := O) encode decode low high lowSafe highSafe s budget sizes
  have selector := RationalSelection.selector_input_cost (O := O) ((s high).length - (s low).length)
    ((s high).length - (s 22).length) ((s 17).map decode) positive ordered
    (by simpa only [List.length_map] using enough)
  have highBound := sizes high
  have bitBound := sizes 17
  have denominator : (s high).length - (s low).length ≤ budget := (Nat.sub_le _ _).trans highBound
  have square : ((s high).length - (s low).length + ((s 17).map decode).length + 1)^2 ≤ (2*(budget+1))^2 := by
    apply Nat.pow_le_pow_left
    simp only [List.length_map]
    omega
  rw [routine_cost]
  change (RationalSelection.selector (O := O)).cost (input decode low high s) ≤ _ at selector
  nlinarith


/-- The surrounding phase may keep a larger common cap: only the selector's
private bank needs room for its own explicit output bound. -/
theorem routine_bound (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) (budget : ℕ) (sizes : StoreBound s budget)
    (positive : 0 < (s high).length - (s low).length)
    (ordered : (s high).length - (s 22).length ≤ (s high).length - (s low).length)
    (enough : Nat.clog 2 ((s high).length - (s low).length) ≤ (s 17).length)
    (room : 20 * ((s high).length - (s low).length + (s 17).length + 1) ≤ budget) :
    StoreBound ((routine (O := O) encode decode retract low high lowSafe highSafe).eval s) budget := by
  intro j
  by_cases owned : j.val < 16
  · let privateIndex : Fin 16 := ⟨j.val, owned⟩
    have same : slots privateIndex = j := by apply Fin.ext; rfl
    rw [← same]
    exact (routine_owned_bound encode decode retract low high lowSafe highSafe s positive ordered enough privateIndex).trans room
  · by_cases scratch : j = 33
    · subst j
      rw [routine_scratch]
      simp
    · rw [routine_frame encode decode retract low high lowSafe highSafe s j (by omega) scratch]
      exact sizes j

end ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection
