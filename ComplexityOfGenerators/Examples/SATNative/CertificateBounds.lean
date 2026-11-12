import ComplexityOfGenerators.Examples.SATNative.AssignmentBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem certificateLength_bound {O : Type} (s : Store) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) : stackBound budget ((LengthTest.routine (O := O) certificateSlots .one).eval s) := by
  intro j
  rw [LengthTest.routine_eval]
  by_cases a : j = 9 <;> by_cases b : j = 22 <;> by_cases c : j = 23 <;> by_cases d : j = 27 <;>
    simp [certificateSlots, a, b, c, d] <;> (try split_ifs) <;> (try simp only [List.length_singleton, List.length_nil]) <;>
    first | exact sizes _ | omega

theorem bitPrefix_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((bitPrefix (O := O)).eval s) := by
  have prefixLength : ((s 3).takeWhile isBit).length ≤ (s 3).length := (List.takeWhile_sublist isBit).length_le
  have suffixLength : ((s 3).dropWhile isBit).length ≤ (s 3).length := (List.dropWhile_sublist isBit).length_le
  intro j
  rw [bitPrefix_eval]
  by_cases a : j = 9 <;> by_cases b : j = 25 <;> by_cases c : j = 24 <;>
    simp [a, b, c] <;> first | exact sizes _ | have := sizes 3; omega

theorem bitPrefix_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (bitPrefix (O := O)).cost s ≤ 30 * (budget + 1) := by
  have clearSize := sizes 24
  have sourceSize := sizes 3
  have targetSize := sizes 25
  have scratchSize := sizes 9
  have prefixLength : ((s 3).takeWhile isBit).length ≤ (s 3).length := (List.takeWhile_sublist isBit).length_le
  simp only [bitPrefix, Routine.seq, Routine.clear, Routine.assign_cost, Routine.assign_eval,
    Routine.transferWhile]
  simp only [Function.update_of_ne (show (3 : Fin 32) ≠ 24 by decide), Function.update_of_ne (show (25 : Fin 32) ≠ 24 by decide),
    Function.update_of_ne (show (9 : Fin 32) ≠ 24 by decide), Function.update_self, List.map_id]
  omega

theorem certificateCheck_bound {O : Type} (s : Store) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) : stackBound budget ((certificateCheck (O := O)).eval s) := by
  let first := (LengthTest.routine (O := O) certificateSlots .one).eval s
  let second := (bitPrefix (O := O)).eval first
  have firstBound := certificateLength_bound (O := O) s budget positive sizes
  have secondBound := bitPrefix_bound (O := O) first budget firstBound
  intro j
  by_cases result : j = 27
  · subst j
    rw [certificateCheck_result]
    split_ifs <;> simp <;> omega
  · change ((LengthTest.finishCode (25 : Fin 32) 27).eval second j).length ≤ _
    rw [LengthTest.finish_eval, Function.update_of_ne result]
    exact secondBound j

theorem certificateCheck_cost {O : Type} (s : Store) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) : (certificateCheck (O := O)).cost s ≤ 120 * (budget + 1) := by
  let first := (LengthTest.routine (O := O) certificateSlots .one).eval s
  let second := (bitPrefix (O := O)).eval first
  have firstBound := certificateLength_bound (O := O) s budget positive sizes
  have one := LengthTest.routine_cost (O := O) certificateSlots .one s budget sizes
  have two := bitPrefix_cost (O := O) first budget firstBound
  have three := LengthTest.finish_ticks (25 : Fin 32) 27 second
  change (LengthTest.routine (O := O) certificateSlots .one).cost s + 1 +
    ((bitPrefix (O := O)).cost first + 1 + (LengthTest.finishCode (25 : Fin 32) 27).ticks second) ≤ _
  omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment
