import ComplexityOfGenerators.Examples.SATNative.VerifierRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody
open NativeAssignment

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prepareEvaluation evaluationChoice evaluationRoutine
  NativeParser.header NativeParser.bodySetup certificateCheck

theorem clear_bound {O : Type} (j : Fin 32) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((Routine.clear (O := O) j).eval s) := by
  intro i
  by_cases changed : i = j <;> simp [Routine.clear, changed] <;> exact sizes i

theorem prepareEvaluation_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound (budget + 1) ((prepareEvaluation (O := O)).eval s) := by
  rw [prepareEvaluation_eval]
  have first := NativeParser.header_bound (O := O) s budget sizes
  have second := NativeParser.bodySetup_bound (O := O) _ (budget + 1) first
  have third := clear_bound (O := O) 20 _ (budget + 1) second
  exact certificateCheck_bound _ (budget + 1) (by omega) third

theorem prepareEvaluation_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (prepareEvaluation (O := O)).cost s ≤ 250 * (budget + 2) := by
  let first := (NativeParser.header (O := O)).eval s
  let second := (NativeParser.bodySetup (O := O)).eval first
  let third := Function.update second 20 ([] : List Symbol)
  have firstBound := NativeParser.header_bound (O := O) s budget sizes
  have secondBound := NativeParser.bodySetup_bound (O := O) first (budget + 1) firstBound
  have thirdBound := clear_bound (O := O) 20 second (budget + 1) secondBound
  have one := NativeParser.header_cost (O := O) s budget sizes
  have two := NativeParser.bodySetup_cost (O := O) first (budget + 1) firstBound
  have three := secondBound 20
  change (second 20).length ≤ budget + 1 at three
  have four := certificateCheck_cost (O := O) third (budget + 1) (by omega) thirdBound
  unfold prepareEvaluation
  change (NativeParser.header (O := O)).cost s + 1 +
    ((NativeParser.bodySetup (O := O)).cost first + 1 +
    (3 * (second 20).length + 1 + (certificateCheck (O := O)).cost third)) ≤ _
  omega

set_option maxHeartbeats 800000 in
theorem verifier_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (verifier (O := O)).cost s ≤ (NativeEvaluation.stepConstant + 400) * (budget + 2)^2 := by
  let ready := (prepareEvaluation (O := O)).eval s
  have readyBound := prepareEvaluation_bound (O := O) s budget sizes
  have properties := prepareEvaluation_properties (O := O) s
  dsimp only at properties
  rcases properties with ⟨represented, clock, _⟩
  have headerSizes := NativeHeader.parsedState_bounds (s 2)
  have capSizes := readOnes_lengths (s 2)
  have sourceSize := sizes 2
  have cap : (readOnes (s 2)).1 ≤ budget + 1 := by omega
  have active : (NativeHeader.parsedState (s 2)).count + 1 ≤ budget + 1 := by omega
  have one := prepareEvaluation_cost (O := O) s budget sizes
  have two := evaluationRoutine_cost (O := O) _ _ _ _ ready represented (budget + 1) (by omega) readyBound cap active
  have clockBound : (ready 16).length ≤ budget := by rw [clock]; omega
  have evaluationBound : (evaluationRoutine (O := O)).cost ready ≤
      budget * ((NativeEvaluation.stepConstant + 4) * (budget + 2)) :=
    two.trans (Nat.mul_le_mul_right _ clockBound)
  have invalidBound := readyBound 6
  change (prepareEvaluation (O := O)).cost s + 1 + (evaluationChoice (O := O)).cost ready ≤ _
  simp only [evaluationChoice, Routine.branch]
  by_cases good : (ready 27).head?.isSome
  · rw [if_pos good]
    nlinarith [Nat.zero_le (NativeEvaluation.stepConstant * (budget + 2))]
  · rw [if_neg good]
    simp only [Routine.clear]
    nlinarith [Nat.zero_le (NativeEvaluation.stepConstant * (budget + 2)^2)]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
