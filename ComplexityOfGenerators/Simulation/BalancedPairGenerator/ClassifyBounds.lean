import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Components
import ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection
import ComplexityOfGenerators.Simulation.UnionGenerator.Bounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

structure ClassifyData (B K cap : ℕ) (s : Store G) : Prop where
  sizes : StoreBound s cap
  left : (s 25).length ≤ B
  right : (s 26).length ≤ B
  enough : B ≤ (s 17).length
  bits : (s 17).length ≤ K

namespace ClassifyData

variable {G} {B K cap : ℕ} {s : Store G}

theorem of_frame (data : ClassifyData G B K cap s) (t : Store G) (sizes : StoreBound t cap)
    (frame : ∀ j : Fin 35, j = 17 ∨ j = 22 ∨ j = 25 ∨ j = 26 → t j = s j) :
    ClassifyData G B K cap t := by
  constructor
  · exact sizes
  · simpa only [frame 25 (by simp)] using data.left
  · simpa only [frame 26 (by simp)] using data.right
  · simpa only [frame 17 (by simp)] using data.enough
  · simpa only [frame 17 (by simp)] using data.bits

theorem comparison (data : ClassifyData G B K cap s) (positive : 1 ≤ cap)
    (flag : Fin 35) (safe : flag ≠ 17 ∧ flag ≠ 22 ∧ flag ≠ 25 ∧ flag ≠ 26)
    (word : List (Cell G)) (size : word.length ≤ 1) :
    ClassifyData G B K cap
      (Function.update (Function.update (Function.update (Function.update s 2 []) 1 []) 0 []) flag word) := by
  apply data.of_frame
  · exact (((data.sizes.clear 2).clear 1).clear 0).update flag word (size.trans positive)
  · intro j member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [safe.1.symm, safe.2.1.symm, safe.2.2.1.symm, safe.2.2.2.symm]

end ClassifyData

theorem equalLeft_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((equalLeft G).eval s) ∧ (equalLeft G).cost s ≤ 80 * (cap + 1) := by
  constructor
  · rw [equalLeft, LengthTest.routine_eval]
    apply data.comparison positive 23 (by decide)
    split_ifs <;> simp
  · exact LengthTest.routine_cost _ _ s cap data.sizes

theorem equalRight_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((equalRight G).eval s) ∧ (equalRight G).cost s ≤ 80 * (cap + 1) := by
  constructor
  · rw [equalRight, LengthTest.routine_eval]
    apply data.comparison positive 24 (by decide)
    split_ifs <;> simp
  · exact LengthTest.routine_cost _ _ s cap data.sizes

theorem leftBelow_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((leftBelow G).eval s) ∧ (leftBelow G).cost s ≤ 80 * (cap + 1) := by
  constructor
  · rw [leftBelow, RationalSelection.Compare.routine_eval]
    apply data.comparison positive 23 (by decide)
    split_ifs <;> simp
  · exact RationalSelection.Compare.routine_cost _ _ s cap data.sizes

theorem rightAbove_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((rightAbove G).eval s) ∧ (rightAbove G).cost s ≤ 80 * (cap + 1) := by
  constructor
  · rw [rightAbove, RationalSelection.Compare.routine_eval]
    apply data.comparison positive 24 (by decide)
    split_ifs <;> simp
  · exact RationalSelection.Compare.routine_cost _ _ s cap data.sizes

theorem rightBelow_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((rightBelow G).eval s) ∧ (rightBelow G).cost s ≤ 80 * (cap + 1) := by
  constructor
  · rw [rightBelow, RationalSelection.Compare.routine_eval]
    apply data.comparison positive 23 (by decide)
    split_ifs <;> simp
  · exact RationalSelection.Compare.routine_cost _ _ s cap data.sizes

theorem leftAbove_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((leftAbove G).eval s) ∧ (leftAbove G).cost s ≤ 80 * (cap + 1) := by
  constructor
  · rw [leftAbove, RationalSelection.Compare.routine_eval]
    apply data.comparison positive 24 (by decide)
    split_ifs <;> simp
  · exact RationalSelection.Compare.routine_cost _ _ s cap data.sizes

theorem pick_bound {B K cap : ℕ} (word : Fin 35) (different : word ≠ 31 ∧ word ≠ 33)
    (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((pick G word different).eval s) ∧ (pick G word different).cost s ≤ 23 * cap + 6 := by
  have assigned := data.sizes.assign (O := α) word 31 33 different.1 different.2 (by decide) id
  obtain ⟨flagged, flagCost⟩ := UnionGenerator.flag_bound G G 32 true _ cap assigned positive
  constructor
  · apply data.of_frame _ flagged
    intro j member
    rcases member with rfl | rfl | rfl | rfl <;> simp [UnionGenerator.flag_eval, Routine.assign_eval]
  · have source := data.sizes word
    have output := data.sizes 31
    have scratch := data.sizes 33
    simp only [pick, Routine.seq, Routine.assign_cost]
    omega

/-- Two flag inspections add at most two primitive instructions. -/
theorem both_bound {B K cap : ℕ} (first second : Fin 35) (yes no : Controller G) (s : Store G) (budget : ℕ)
    (yesBound : (s first).head?.isSome = true → (s second).head?.isSome = true →
      ClassifyData G B K cap (yes.eval s) ∧ yes.cost s ≤ budget)
    (noBound : ClassifyData G B K cap (no.eval s) ∧ no.cost s ≤ budget) :
    ClassifyData G B K cap ((both G first second yes no).eval s) ∧
      (both G first second yes no).cost s ≤ budget + 2 := by
  by_cases one : (s first).head?.isSome = true
  · by_cases two : (s second).head?.isSome = true
    · obtain ⟨bounded, cost⟩ := yesBound one two
      constructor
      · simpa only [both, Routine.branch, ite_eq_left one, ite_eq_left two] using bounded
      · simp only [both, Routine.branch, ite_eq_left one, ite_eq_left two]
        omega
    · constructor
      · simpa only [both, Routine.branch, ite_eq_left one, ite_eq_right two] using noBound.1
      · simp only [both, Routine.branch, ite_eq_left one, ite_eq_right two]
        have := noBound.2
        omega
  · constructor
    · simpa only [both, Routine.branch, ite_eq_right one] using noBound.1
    · simp only [both, Routine.branch, ite_eq_right one]
      have := noBound.2
      omega


theorem select_bound {B K cap : ℕ} (low high : Fin 35)
    (lowSafe : PreparedRationalSelection.Safe low) (highSafe : PreparedRationalSelection.Safe high)
    (s : Store G) (data : ClassifyData G B K cap s)
    (highBound : (s high).length ≤ B)
    (below : (s low).length < (s 22).length) (above : (s 22).length < (s high).length)
    (room : 20 * (B + K + 1) ≤ cap) :
    ClassifyData G B K cap ((select G low high lowSafe highSafe).eval s) ∧
      (select G low high lowSafe highSafe).cost s ≤ 100000 * (cap + 1)^2 := by
  have positive : 0 < (s high).length - (s low).length := by omega
  have ordered : (s high).length - (s 22).length ≤ (s high).length - (s low).length := by omega
  have enough : Nat.clog 2 ((s high).length - (s low).length) ≤ (s 17).length :=
    (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by
      have := data.enough
      omega)
  have selectorRoom : 20 * ((s high).length - (s low).length + (s 17).length + 1) ≤ cap := by
    have := data.bits
    omega
  have bounded := PreparedRationalSelection.routine_bound (O := α) Symbol.bit (decodeBit G) (fun _ => rfl)
    low high lowSafe highSafe s cap data.sizes positive ordered enough selectorRoom
  constructor
  · apply data.of_frame _ bounded
    intro j member
    apply PreparedRationalSelection.routine_frame
    · rcases member with rfl | rfl | rfl | rfl <;> decide
    · rcases member with rfl | rfl | rfl | rfl <;> decide
  · exact PreparedRationalSelection.routine_cost_le _ _ _ low high lowSafe highSafe s cap data.sizes
      positive ordered enough

theorem selectionFinish_bound {B K cap : ℕ} (low high : Fin 35)
    (lowDifferent : low ≠ 31 ∧ low ≠ 33) (highDifferent : high ≠ 31 ∧ high ≠ 33)
    (s : Store G) (data : ClassifyData G B K cap s) (positive : 1 ≤ cap) :
    ClassifyData G B K cap ((selectionFinish G low high lowDifferent highDifferent).eval s) ∧
      (selectionFinish G low high lowDifferent highDifferent).cost s ≤ 23 * cap + 8 := by
  by_cases valid : (s 12).head?.isSome = true
  · by_cases choice : (s 13).head?.isSome = true
    · obtain ⟨bounded, cost⟩ := pick_bound G low lowDifferent s data positive
      constructor
      · simpa only [selectionFinish, Routine.branch, ite_eq_left valid, ite_eq_left choice] using bounded
      · simp only [selectionFinish, Routine.branch, ite_eq_left valid, ite_eq_left choice]
        omega
    · obtain ⟨bounded, cost⟩ := pick_bound G high highDifferent s data positive
      constructor
      · simpa only [selectionFinish, Routine.branch, ite_eq_left valid, ite_eq_right choice] using bounded
      · simp only [selectionFinish, Routine.branch, ite_eq_left valid, ite_eq_right choice]
        omega
  · constructor
    · simpa only [selectionFinish, Routine.branch, ite_eq_right valid, Routine.skip, Routine.ofLocal, Local.eval] using data
    · simp only [selectionFinish, Routine.branch, ite_eq_right valid, Routine.skip, Routine.ofLocal, Local.ticks]
      omega


theorem weightedLeft_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s)
    (below : (s 25).length < (s 22).length) (above : (s 22).length < (s 26).length)
    (room : 20 * (B + K + 1) ≤ cap) :
    ClassifyData G B K cap ((weightedLeft G).eval s) ∧
      (weightedLeft G).cost s ≤ 200000 * (cap + 1)^2 := by
  obtain ⟨selected, selectCost⟩ := select_bound G 25 26 (by decide) (by decide) s data data.right below above room
  obtain ⟨finished, finishCost⟩ := selectionFinish_bound G 25 26 (by decide) (by decide) _ selected (by omega)
  refine ⟨finished, ?_⟩
  change (select G 25 26 (by decide) (by decide)).cost s + 1 +
    (selectionFinish G 25 26 (by decide) (by decide)).cost _ ≤ _
  nlinarith

theorem weightedRight_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s)
    (below : (s 26).length < (s 22).length) (above : (s 22).length < (s 25).length)
    (room : 20 * (B + K + 1) ≤ cap) :
    ClassifyData G B K cap ((weightedRight G).eval s) ∧
      (weightedRight G).cost s ≤ 200000 * (cap + 1)^2 := by
  obtain ⟨selected, selectCost⟩ := select_bound G 26 25 (by decide) (by decide) s data data.left below above room
  obtain ⟨finished, finishCost⟩ := selectionFinish_bound G 26 25 (by decide) (by decide) _ selected (by omega)
  refine ⟨finished, ?_⟩
  change (select G 26 25 (by decide) (by decide)).cost s + 1 +
    (selectionFinish G 26 25 (by decide) (by decide)).cost _ ≤ _
  nlinarith


theorem reverseCase_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s)
    (room : 20 * (B + K + 1) ≤ cap) :
    ClassifyData G B K cap ((reverseCase G).eval s) ∧
      (reverseCase G).cost s ≤ 300000 * (cap + 1)^2 := by
  obtain ⟨firstData, firstCost⟩ := rightBelow_bound G s data (by omega)
  obtain ⟨secondData, secondCost⟩ := leftAbove_bound G _ firstData (by omega)
  let middle := (leftAbove G).eval ((rightBelow G).eval s)
  have weighted : (middle 23).head?.isSome = true → (middle 24).head?.isSome = true →
      ClassifyData G B K cap ((weightedRight G).eval middle) ∧
        (weightedRight G).cost middle ≤ 200000 * (cap + 1)^2 := by
    intro low high
    have below : (s 26).length < (s 22).length := by
      by_contra absent
      simp [middle, rightBelow, leftAbove, RationalSelection.Compare.routine_eval, absent] at low
    have above : (s 22).length < (s 25).length := by
      by_contra absent
      simp [middle, rightBelow, leftAbove, RationalSelection.Compare.routine_eval, absent] at high
    apply weightedRight_bound G middle secondData _ _ room
    · simpa [middle, rightBelow, leftAbove, RationalSelection.Compare.routine_eval] using below
    · simpa [middle, rightBelow, leftAbove, RationalSelection.Compare.routine_eval] using above
  obtain ⟨chosen, choiceCost⟩ := both_bound G 23 24 (weightedRight G) Routine.skip middle
    (200000 * (cap + 1)^2) weighted ⟨secondData, by simp [Routine.skip, Routine.ofLocal, Local.ticks]⟩
  refine ⟨chosen, ?_⟩
  change (rightBelow G).cost s + 1 + ((leftAbove G).cost _ + 1 +
    (both G 23 24 (weightedRight G) Routine.skip).cost middle) ≤ _
  nlinarith

theorem strictCases_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s)
    (room : 20 * (B + K + 1) ≤ cap) :
    ClassifyData G B K cap ((strictCases G).eval s) ∧
      (strictCases G).cost s ≤ 400000 * (cap + 1)^2 := by
  obtain ⟨firstData, firstCost⟩ := leftBelow_bound G s data (by omega)
  obtain ⟨secondData, secondCost⟩ := rightAbove_bound G _ firstData (by omega)
  let middle := (rightAbove G).eval ((leftBelow G).eval s)
  have weighted : (middle 23).head?.isSome = true → (middle 24).head?.isSome = true →
      ClassifyData G B K cap ((weightedLeft G).eval middle) ∧
        (weightedLeft G).cost middle ≤ 300000 * (cap + 1)^2 := by
    intro low high
    have below : (s 25).length < (s 22).length := by
      by_contra absent
      simp [middle, leftBelow, rightAbove, RationalSelection.Compare.routine_eval, absent] at low
    have above : (s 22).length < (s 26).length := by
      by_contra absent
      simp [middle, leftBelow, rightAbove, RationalSelection.Compare.routine_eval, absent] at high
    obtain ⟨bounded, cost⟩ := weightedLeft_bound G middle secondData
      (by simpa [middle, leftBelow, rightAbove, RationalSelection.Compare.routine_eval] using below)
      (by simpa [middle, leftBelow, rightAbove, RationalSelection.Compare.routine_eval] using above) room
    exact ⟨bounded, by nlinarith⟩
  have reversed := reverseCase_bound G middle secondData room
  obtain ⟨chosen, choiceCost⟩ := both_bound G 23 24 (weightedLeft G) (reverseCase G) middle
    (300000 * (cap + 1)^2) weighted reversed
  refine ⟨chosen, ?_⟩
  change (leftBelow G).cost s + 1 + ((rightAbove G).cost _ + 1 +
    (both G 23 24 (weightedLeft G) (reverseCase G)).cost middle) ≤ _
  nlinarith

theorem equalCase_bound {B K cap : ℕ} (s : Store G) (data : ClassifyData G B K cap s)
    (room : 20 * (B + K + 1) ≤ cap) :
    ClassifyData G B K cap ((equalCase G).eval s) ∧
      (equalCase G).cost s ≤ 500000 * (cap + 1)^2 := by
  obtain ⟨firstData, firstCost⟩ := equalLeft_bound G s data (by omega)
  obtain ⟨secondData, secondCost⟩ := equalRight_bound G _ firstData (by omega)
  let middle := (equalRight G).eval ((equalLeft G).eval s)
  have picked : (middle 23).head?.isSome = true → (middle 24).head?.isSome = true →
      ClassifyData G B K cap ((pick G 25 (by decide)).eval middle) ∧
        (pick G 25 (by decide)).cost middle ≤ 400000 * (cap + 1)^2 := by
    intro _ _
    obtain ⟨bounded, cost⟩ := pick_bound G 25 (by decide) middle secondData (by omega)
    exact ⟨bounded, by nlinarith⟩
  have strict := strictCases_bound G middle secondData room
  obtain ⟨chosen, choiceCost⟩ := both_bound G 23 24 (pick G 25 (by decide)) (strictCases G) middle
    (400000 * (cap + 1)^2) picked strict
  refine ⟨chosen, ?_⟩
  change (equalLeft G).cost s + 1 + ((equalRight G).cost _ + 1 +
    (both G 23 24 (pick G 25 (by decide)) (strictCases G)).cost middle) ≤ _
  nlinarith

/-- Complete classifier bounds require no payload or success-flag invariant.
Only strict comparison branches enter the bounded rational selector. -/
theorem classify_bound (B K cap : ℕ) (s : Store G) (sizes : StoreBound s cap)
    (left : (s 25).length ≤ B) (right : (s 26).length ≤ B)
    (enough : B ≤ (s 17).length) (bits : (s 17).length ≤ K)
    (room : 20 * (B + K + 1) ≤ cap) :
    StoreBound ((classify G).eval s) cap ∧ (classify G).cost s ≤ 1000000 * (cap + 1)^2 := by
  let data : ClassifyData G B K cap s := ⟨sizes, left, right, enough, bits⟩
  have yes := equalCase_bound G s data room
  have bounded := both_bound G 27 28 (equalCase G) Routine.skip s (500000 * (cap + 1)^2)
    (fun _ _ => yes) ⟨data, by simp [Routine.skip, Routine.ofLocal, Local.ticks]⟩
  exact ⟨bounded.1.sizes, by change (both G 27 28 (equalCase G) Routine.skip).cost s ≤ _; nlinarith [bounded.2]⟩


theorem both_fixes (first second : Fin 35) (yes no : Controller G) (j : Fin 35)
    (one : yes.Fixes j) (two : no.Fixes j) : (both G first second yes no).Fixes j := by
  intro s
  by_cases left : (s first).head?.isSome = true
  · by_cases right : (s second).head?.isSome = true
    · simpa only [both, Routine.branch, ite_eq_left left, ite_eq_left right] using one s
    · simpa only [both, Routine.branch, ite_eq_left left, ite_eq_right right] using two s
  · simpa only [both, Routine.branch, ite_eq_right left] using two s

theorem pick_fixes22 (word : Fin 35) (different : word ≠ 31 ∧ word ≠ 33) : (pick G word different).Fixes 22 := by
  intro s
  simp [pick_eval]

theorem selectionFinish_fixes22 (low high : Fin 35)
    (lowDifferent : low ≠ 31 ∧ low ≠ 33) (highDifferent : high ≠ 31 ∧ high ≠ 33) :
    (selectionFinish G low high lowDifferent highDifferent).Fixes 22 := by
  intro s
  by_cases valid : (s 12).head?.isSome = true
  · by_cases choice : (s 13).head?.isSome = true
    · simpa only [selectionFinish, Routine.branch, ite_eq_left valid, ite_eq_left choice] using
        pick_fixes22 G low lowDifferent s
    · simpa only [selectionFinish, Routine.branch, ite_eq_left valid, ite_eq_right choice] using
        pick_fixes22 G high highDifferent s
  · simp only [selectionFinish, Routine.branch, ite_eq_right valid, Routine.skip, Routine.ofLocal, Local.eval]

theorem select_fixes22 (low high : Fin 35) (lowSafe : PreparedRationalSelection.Safe low)
    (highSafe : PreparedRationalSelection.Safe high) : (select G low high lowSafe highSafe).Fixes 22 := by
  intro s
  exact PreparedRationalSelection.routine_frame _ _ _ low high lowSafe highSafe s 22 (by decide) (by decide)

theorem weightedLeft_fixes22 : (weightedLeft G).Fixes 22 :=
  (select_fixes22 G 25 26 (by decide) (by decide)).seq
    (selectionFinish_fixes22 G 25 26 (by decide) (by decide))

theorem weightedRight_fixes22 : (weightedRight G).Fixes 22 :=
  (select_fixes22 G 26 25 (by decide) (by decide)).seq
    (selectionFinish_fixes22 G 26 25 (by decide) (by decide))

theorem reverseCase_fixes22 : (reverseCase G).Fixes 22 := by
  have first : (rightBelow G).Fixes 22 := by intro s; simp [rightBelow, RationalSelection.Compare.routine_eval]
  have second : (leftAbove G).Fixes 22 := by intro s; simp [leftAbove, RationalSelection.Compare.routine_eval]
  exact first.seq (second.seq (both_fixes G 23 24 _ _ 22 (weightedRight_fixes22 G) (Routine.fixes_skip 22)))

theorem strictCases_fixes22 : (strictCases G).Fixes 22 := by
  have first : (leftBelow G).Fixes 22 := by intro s; simp [leftBelow, RationalSelection.Compare.routine_eval]
  have second : (rightAbove G).Fixes 22 := by intro s; simp [rightAbove, RationalSelection.Compare.routine_eval]
  exact first.seq (second.seq (both_fixes G 23 24 _ _ 22 (weightedLeft_fixes22 G) (reverseCase_fixes22 G)))

theorem equalCase_fixes22 : (equalCase G).Fixes 22 := by
  have first : (equalLeft G).Fixes 22 := by intro s; simp [equalLeft, LengthTest.routine_eval]
  have second : (equalRight G).Fixes 22 := by intro s; simp [equalRight, LengthTest.routine_eval]
  exact first.seq (second.seq (both_fixes G 23 24 _ _ 22 (pick_fixes22 G 25 (by decide)) (strictCases_fixes22 G)))

/-- The retry loop's master index is preserved by every classification path. -/
theorem classify_fixes22 : (classify G).Fixes 22 :=
  both_fixes G 27 28 _ _ 22 (equalCase_fixes22 G) (Routine.fixes_skip 22)

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
