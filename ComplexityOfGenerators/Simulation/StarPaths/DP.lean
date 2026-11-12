import ComplexityOfGenerators.Simulation.StarPaths.Iteration
import ComplexityOfGenerators.Simulation.StarPaths.Correctness

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] stageSetup stageRoutine appendEntry outerBody prepare dpRoutine

def DPRep (flags : List Bool) (n : ℕ) (s : Store) : Prop :=
  s 1 = List.replicate n .unit ∧ s 4 = encoded (archive flags n) ∧ s 25 = flagsWord flags ∧
    s 10 = held (fallback flags n) ∧ s 11 = flagWord (fallback flags n).isSome

theorem outerBody_represents {O : Type} (flags : List Bool) (n : ℕ) (s : Store)
    (represented : DPRep flags n s) : DPRep flags (n+1) ((outerBody (O := O)).eval s) := by
  rcases represented with ⟨counter,table,source,_,_⟩
  let pushed := Function.update s 1 (.unit::s 1)
  let prepared := (stageSetup (O := O)).eval pushed
  let walked := (stageRoutine (O := O)).eval prepared
  have preparedRep : StageRep flags (archive flags n) 1 none prepared := by
    apply stageSetup_represents
    · simpa [pushed] using table
    · simpa [pushed] using source
  have preparedClock : (prepared 2).length = (archive flags n).length := by
    rw [stageSetup_clock]
    simp [pushed,counter]
  have result := stageRoutine_result (O := O) flags (archive flags n) prepared preparedRep preparedClock
  have setupFrame (j : Fin 35) (a : j ≠ 2) (b : j ≠ 3) (c : j ≠ 5) (d : j ≠ 6)
      (e : j ≠ 10) (f : j ≠ 11) (g : j ≠ 12) : prepared j = pushed j := stageSetup_frame j a b c d e f g pushed
  have loopFrame (j : Fin 35) (a : j ≠ 2) (b : j ≠ 3) (c : j ≠ 5) (d : j ≠ 6)
      (e : j ≠ 7) (f : j ≠ 8) (g : j ≠ 9) (h : j ≠ 10) (i : j ≠ 11) (k : j ≠ 12) :
      walked j = prepared j := stageRoutine_frame j a b c d e f g h i k prepared
  have walkedCounter : walked 1 = List.replicate (n+1) .unit := by
    rw [loopFrame 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),setupFrame 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    simp [pushed,counter,List.replicate_succ]
  have walkedTable : walked 4 = encoded (archive flags n) := by
    rw [loopFrame 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),setupFrame 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    simpa [pushed] using table
  have walkedSource : walked 25 = flagsWord flags := by
    rw [loopFrame 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),setupFrame 25 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    simpa [pushed] using source
  have finalTable := appendEntry_archive (O := O) (stage flags (archive flags n)) walked result.1 result.2
  have actual : (outerBody (O := O)).eval s = (appendEntry (O := O)).eval walked := by unfold outerBody; rfl
  have finalFrame (j : Fin 35) (a : j ≠ 4) (b : j ≠ 12) :
      (appendEntry (O := O)).eval walked j = walked j := appendEntry_frame j a b walked
  rw [actual]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (finalFrame 1 (by decide) (by decide)).trans walkedCounter
  · rw [finalTable,walkedTable]
    rfl
  · exact (finalFrame 25 (by decide) (by decide)).trans walkedSource
  · rw [finalFrame 10 (by decide) (by decide)]
    exact result.1
  · rw [finalFrame 11 (by decide) (by decide)]
    exact result.2

private theorem dpRep_pop (flags : List Bool) (n : ℕ) (s : Store) (represented : DPRep flags n s) :
    DPRep flags n (Function.update s 0 (s 0).tail) := by simpa [DPRep] using represented

theorem counted_dp {O : Type} (flags : List Bool) (n count : ℕ) (s : Store) (represented : DPRep flags n s) :
    DPRep flags (n+count) ((WordStack.Routine.counted 0 (outerBody (O := O))).eval^[count] s) := by
  induction count generalizing n s with
  | zero => simpa using represented
  | succ count ih =>
      let ready := (WordStack.Routine.counted 0 (outerBody (O := O))).eval s
      have first := outerBody_represents (O := O) flags n (Function.update s 0 (s 0).tail) (dpRep_pop flags n s represented)
      have result := ih (n+1) ready first
      simpa only [Function.iterate_succ_apply,Nat.add_assoc,Nat.add_comm 1 count] using result

theorem prepare_represents {O : Type} (flags : List Bool) (s : Store) (source : s 25 = flagsWord flags) :
    DPRep flags 0 ((prepare (O := O)).eval s) ∧ ((prepare (O := O)).eval s 0).length = (s 22).length := by
  simp [DPRep,prepare,WordStack.Routine.seq,WordStack.Routine.clearMany_eval,owned,
    WordStack.Routine.assign_eval,WordStack.Routine.ofLocal,Local.eval_push,source,archive,fallback,
    encoded,entry,held,payload,flagWord]

/-- The finite native DP computes a genuine fallback composition and reports
none exactly when the cached availability vector admits no composition. -/
theorem dpRoutine_result {O : Type} (flags : List Bool) (s : Store) (source : s 25 = flagsWord flags) :
    (dpRoutine (O := O)).eval s 10 = held (fallback flags (s 22).length) ∧
      (dpRoutine (O := O)).eval s 11 = flagWord (fallback flags (s 22).length).isSome := by
  have initialized := prepare_represents (O := O) flags s source
  have result := counted_dp (O := O) flags 0 (s 22).length _ initialized.1
  have actual : (dpRoutine (O := O)).eval s =
      ((WordStack.Routine.counted 0 (outerBody (O := O))).eval^[(s 22).length]) ((prepare (O := O)).eval s) := by
    unfold dpRoutine
    change ((WordStack.Routine.counted 0 (outerBody (O := O))).eval^[((prepare (O := O)).eval s 0).length])
      ((prepare (O := O)).eval s) = _
    rw [initialized.2]
  rw [actual]
  constructor
  · simpa only [Nat.zero_add] using result.2.2.2.1
  · simpa only [Nat.zero_add] using result.2.2.2.2

end ComplexityOfGenerators.Simulation.StarPaths
