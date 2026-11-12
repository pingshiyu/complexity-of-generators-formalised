import ComplexityOfGenerators.Simulation.StarPaths.PrimitiveBounds
import ComplexityOfGenerators.Simulation.StarPaths.DP
import ComplexityOfGenerators.Simulation.WordStack.GrowingRoutine

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem stageBody_counter {O : Type} (s : Store) :
    ((stageBody (O := O)).eval s 3).length = (s 3).length+1 := by
  let pushed := Function.update s 3 (Symbol.unit::s 3)
  change ((consider (O := O)).eval ((readEntry (O := O)).eval pushed) 3).length = _
  rw [consider_frame 3 (by decide) (by decide) (by decide),
    readEntry_frame 3 (by decide) (by decide) (by decide) (by decide)]
  simp [pushed]

theorem stageBody_bound {O : Type} (s : Store) (budget extra : ℕ)
    (positive : 1 ≤ budget) (sizes : StoreBound s budget) (counter : (s 3).length ≤ extra) :
    StoreBound ((stageBody (O := O)).eval s) (budget+extra+3) ∧
      (stageBody (O := O)).cost s ≤ 300*(budget+1) := by
  let pushed := Function.update s 3 (Symbol.unit::s 3)
  let decoded := (readEntry (O := O)).eval pushed
  have pushedBound : StoreBound pushed (budget+1) :=
    (sizes.mono (by omega)).update 3 _ (by simpa using Nat.add_le_add_right (sizes 3) 1)
  have read := readEntry_bound (O := O) pushed (budget+1) (by omega) pushedBound
  have decodedCounter : (decoded 3).length ≤ extra+1 := by
    change ((readEntry (O := O)).eval pushed 3).length ≤ extra+1
    rw [readEntry_frame 3 (by decide) (by decide) (by decide) (by decide)]
    simpa [pushed] using Nat.add_le_add_right counter 1
  have considered := consider_bound (O := O) decoded (budget+1) (extra+1) read.1 decodedCounter
  constructor
  · have actual : (stageBody (O := O)).eval s =
        Function.update ((consider (O := O)).eval decoded) 6 (((consider (O := O)).eval decoded) 6).tail := rfl
    rw [actual]
    convert considered.1.update 6 (((consider (O := O)).eval decoded) 6).tail (by
      simpa only [List.length_tail] using (Nat.sub_le (((consider (O := O)).eval decoded) 6).length 1).trans (considered.1 6)) using 1 <;> omega
  · change 1+1+((readEntry (O := O)).cost pushed+1+((consider (O := O)).cost decoded+1+1)) ≤ _
    have readCost := read.2
    have consideredCost := considered.2
    omega

theorem counted_stage_counter {O : Type} (s : Store) (count : ℕ) :
    (((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[count] s) 3).length = (s 3).length+count := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    change ((stageBody (O := O)).eval
      (Function.update ((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[count] s) 2
        (((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[count] s) 2).tail) 3).length = _
    rw [stageBody_counter]
    simpa only [Function.update_of_ne (by decide : (3 : Fin 35) ≠ 2),ih,Nat.add_assoc]

theorem counted_stage_bound {O : Type} (s : Store) (budget extra count : ℕ)
    (positive : 1 ≤ budget) (sizes : StoreBound s budget) (counter : (s 3).length+count ≤ extra) :
    StoreBound ((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[count] s)
      (budget+count*(extra+3)) := by
  induction count with
  | zero => simpa using sizes
  | succ count ih =>
    have prior := ih (by omega)
    let current := (WordStack.Routine.counted 2 (stageBody (O := O))).eval^[count] s
    let popped := Function.update current 2 (current 2).tail
    have poppedBound : StoreBound popped (budget+count*(extra+3)) :=
      prior.update 2 _ (by simpa only [List.length_tail] using (Nat.sub_le (current 2).length 1).trans (prior 2))
    have currentCounter := counted_stage_counter (O := O) s count
    have poppedCounter : (popped 3).length ≤ extra := by
      simp only [popped,Function.update_of_ne (by decide : (3 : Fin 35) ≠ 2)]
      change (current 3).length ≤ extra
      change (current 3).length = _ at currentCounter
      omega
    have next := (stageBody_bound (O := O) popped (budget+count*(extra+3)) extra (by omega) poppedBound poppedCounter).1
    rw [Function.iterate_succ_apply']
    convert next using 1 <;> simp [WordStack.Routine.counted,WordStack.Routine.seq,WordStack.Routine.ofLocal,
      Local.eval_pop,current,popped,Nat.add_mul,Nat.add_assoc]

theorem stageRoutine_bound {O : Type} (s : Store) (budget extra : ℕ)
    (positive : 1 ≤ budget) (sizes : StoreBound s budget) (counter : (s 3).length+(s 2).length ≤ extra) :
    StoreBound ((stageRoutine (O := O)).eval s) (budget+(s 2).length*(extra+3)) ∧
      (stageRoutine (O := O)).cost s ≤ (s 2).length*304*(budget+(s 2).length*(extra+3)+1) := by
  constructor
  · exact counted_stage_bound (O := O) s budget extra (s 2).length positive sizes counter
  · change WordStack.Routine.loopCost _ _ (s 2).length s ≤ _
    apply (WordStack.Routine.loopCost_bound _ _ (s 2).length
      (300*(budget+(s 2).length*(extra+3)+1)+2) s ?_).trans
    · calc
        _ ≤ (s 2).length*(304*(budget+(s 2).length*(extra+3)+1)) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    · intro i inside
      let current := (WordStack.Routine.counted 2 (stageBody (O := O))).eval^[i] s
      let popped := Function.update current 2 (current 2).tail
      have prior := counted_stage_bound (O := O) s budget extra i positive sizes (by omega)
      have upper : budget+i*(extra+3) ≤ budget+(s 2).length*(extra+3) := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt inside)) _
      have poppedBound : StoreBound popped (budget+(s 2).length*(extra+3)) :=
        (prior.mono upper).update 2 _ (by
          simpa only [List.length_tail] using (Nat.sub_le (current 2).length 1).trans ((prior 2).trans upper))
      have currentCounter := counted_stage_counter (O := O) s i
      have poppedCounter : (popped 3).length ≤ extra := by
        simp only [popped,Function.update_of_ne (by decide : (3 : Fin 35) ≠ 2)]
        change (current 3).length ≤ extra
        change (current 3).length = _ at currentCounter
        omega
      have cost := (stageBody_bound (O := O) popped (budget+(s 2).length*(extra+3)) extra
        (by omega) poppedBound poppedCounter).2
      change 1+1+(stageBody (O := O)).cost popped ≤ _
      omega

end ComplexityOfGenerators.Simulation.StarPaths
