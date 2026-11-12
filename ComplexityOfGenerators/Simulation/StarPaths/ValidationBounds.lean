import ComplexityOfGenerators.Simulation.StarPaths.Validation
import ComplexityOfGenerators.Simulation.WordStack.TransferWhileBounds
import ComplexityOfGenerators.Simulation.WordStack.GrowingRoutine

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

private theorem drain_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((DrainPair.routine (O := O) 19 23 21 (by decide) (by decide)).eval s) budget ∧
      (DrainPair.routine (O := O) 19 23 21 (by decide) (by decide)).cost s ≤ 6*budget := by
  constructor
  · rw [DrainPair.routine_eval 19 23 21 (by decide) (by decide) (by decide)]
    exact ((sizes.clear 19).update 23 _ (by simpa only [List.length_drop] using (Nat.sub_le (s 23).length (s 19).length).trans (sizes 23))).update
      21 _ (by simpa only [List.length_drop] using (Nat.sub_le (s 21).length ((s 19).length-(s 23).length)).trans (sizes 21))
  · exact (DrainPair.routine_cost 19 23 21 (by decide) (by decide) s).trans (Nat.mul_le_mul_left 6 (sizes 19))

theorem validationFactor_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((validationFactor (O := O)).eval s) budget ∧
      (validationFactor (O := O)).cost s ≤ 100*(budget+1) := by
  let popped := Function.update s 16 (s 16).tail
  let cleared := Function.update popped 19 []
  let moved := (WordStack.Routine.transferWhile (O := O) 16 19 (by decide) isUnit id).eval cleared
  let shortened := Function.update moved 19 (moved 19).tail
  let assigned := (WordStack.Routine.assign (O := O) 25 23 12 (by decide) (by decide) (by decide) id).eval shortened
  let ready := Function.update assigned 21 []
  let drained := (DrainPair.routine (O := O) 19 23 21 (by decide) (by decide)).eval ready
  have poppedBound : StoreBound popped budget := sizes.update 16 _ (by
    simpa only [List.length_tail] using (Nat.sub_le (s 16).length 1).trans (sizes 16))
  have clearedBound : StoreBound cleared budget := poppedBound.clear 19
  have movedBound : StoreBound moved budget := clearedBound.transferWhile 16 19 (by decide) isUnit id (by simp [cleared])
  have movedCost := WordStack.Routine.transferWhile_cost (O := O) 16 19 (by decide) isUnit id clearedBound
  have shortenedBound : StoreBound shortened budget := movedBound.update 19 _ (by
    simpa only [List.length_tail] using (Nat.sub_le (moved 19).length 1).trans (movedBound 19))
  have assignedBound : StoreBound assigned budget := shortenedBound.assign 25 23 12 (by decide) (by decide) (by decide) id
  have readyBound : StoreBound ready budget := assignedBound.clear 21
  have finished := drain_bound (O := O) ready budget readyBound
  have copying : (WordStack.Routine.assign (O := O) 25 23 12 (by decide) (by decide) (by decide) id).cost shortened ≤
      20*budget+3 := by
    rw [WordStack.Routine.assign_cost]
    have a := shortenedBound 23
    have b := shortenedBound 12
    have c := shortenedBound 25
    omega
  have finishBound : StoreBound ((WordStack.Routine.branch (O := O) 23 fun flag => if available flag then
      WordStack.Routine.skip else WordStack.Routine.clear 20).eval drained) budget := by
    simp only [WordStack.Routine.branch]
    split_ifs
    · exact finished.1
    · exact finished.1.clear 20
  have finishCost : (WordStack.Routine.branch (O := O) 23 fun flag => if available flag then
      WordStack.Routine.skip else WordStack.Routine.clear 20).cost drained ≤ 3*budget+1 := by
    simp only [WordStack.Routine.branch]
    split_ifs <;> simp only [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.ticks,WordStack.Routine.clear]
    · omega
    · have : (drained 20).length ≤ budget := finished.1 20
      omega
  constructor
  · exact finishBound
  · change 1+1+(3*(popped 19).length+1+
      ((WordStack.Routine.transferWhile (O := O) 16 19 (by decide) isUnit id).cost cleared+1+
        (1+1+((WordStack.Routine.assign (O := O) 25 23 12 (by decide) (by decide) (by decide) id).cost shortened+1+
          (3*(assigned 21).length+1+((DrainPair.routine (O := O) 19 23 21 (by decide) (by decide)).cost ready+1+
            (WordStack.Routine.branch (O := O) 23 fun flag => if available flag then WordStack.Routine.skip
              else WordStack.Routine.clear 20).cost drained)))))) ≤ _
    have a := poppedBound 19
    have b := assignedBound 21
    have c := finished.2
    omega

theorem validationBody_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((validationBody (O := O)).eval s) budget ∧
      (validationBody (O := O)).cost s ≤ 110*(budget+1) := by
  by_cases nonempty : (s 16).head?.isSome = true
  · have factor := validationFactor_bound (O := O) s budget sizes
    simp only [validationBody,WordStack.Routine.branch,nonempty,ite_true]
    exact ⟨factor.1,by omega⟩
  · simp only [validationBody,WordStack.Routine.branch,nonempty,Bool.false_eq_true,ite_false]
    exact ⟨sizes,by simp [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.ticks]; omega⟩

theorem validationLoop_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((validationLoop (O := O)).eval s) budget ∧
      (validationLoop (O := O)).cost s ≤ (s 18).length*114*(budget+1) := by
  have preserved := WordStack.Routine.iterate_growing_bound 18 (validationBody (O := O)) (fun _ => True)
    0 0 (by intros; trivial) (by intros; trivial)
    (fun t b _ _ h => by simpa using (validationBody_bound (O := O) t b h).1)
    (validationBody_frame 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    s budget (by omega) trivial sizes
  have cost := WordStack.Routine.iterate_growing_cost 18 (validationBody (O := O)) (fun _ => True)
    0 0 110 (by intros; trivial) (by intros; trivial)
    (fun t b _ _ h => by simpa using (validationBody_bound (O := O) t b h).1)
    (fun t b _ _ h => (validationBody_bound (O := O) t b h).2)
    (validationBody_frame 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    s budget budget (by omega) trivial sizes (by simp)
  exact ⟨by simpa [validationLoop] using preserved.2,by simpa [validationLoop] using cost⟩

theorem validationSetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((validationSetup (O := O)).eval s) (budget+1) ∧
      (validationSetup (O := O)).cost s ≤ 50*(budget+1) := by
  let first := (WordStack.Routine.assign (O := O) 31 16 12 (by decide) (by decide) (by decide) id).eval s
  let second := (WordStack.Routine.assign (O := O) 22 18 12 (by decide) (by decide) (by decide)
    (fun _ => Symbol.unit)).eval first
  have secondBound : StoreBound second budget :=
    (sizes.assign 31 16 12 (by decide) (by decide) (by decide) id).assign
      22 18 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)
  constructor
  · have value : (validationSetup (O := O)).eval s = Function.update second 20 [Symbol.present] := by
      simp [validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
        WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push,first,second]
    rw [value]
    exact (secondBound.mono (by omega)).update 20 _ (by simp)
  · have a := sizes 16
    have b := sizes 12
    have c := sizes 31
    have d := sizes 18
    have e := sizes 22
    have f := sizes 20
    simp [validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_cost,WordStack.Routine.assign_eval,
      WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.push,Local.ticks]
    omega

theorem validationRoutine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((validationRoutine (O := O)).eval s) (budget+1) ∧
      (validationRoutine (O := O)).cost s ≤ 300*(budget+1)^2 := by
  let prepared := (validationSetup (O := O)).eval s
  have setup := validationSetup_bound (O := O) s budget sizes
  have loop := validationLoop_bound (O := O) prepared (budget+1) setup.1
  have clock : (prepared 18).length = (s 22).length := by
    simp [prepared,validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
      WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push]
  refine ⟨loop.1,?_⟩
  have bound : (validationLoop (O := O)).cost prepared ≤ budget*114*(budget+1+1) :=
    loop.2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 114 (by simpa only [clock] using sizes 22)))
  change (validationSetup (O := O)).cost s+1+(validationLoop (O := O)).cost prepared ≤ _
  have cost := setup.2
  nlinarith

end ComplexityOfGenerators.Simulation.StarPaths
