import ComplexityOfGenerators.Simulation.StarPaths.ArchiveBounds
import ComplexityOfGenerators.Simulation.StarPaths.Archive
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

/-! Primitive cost and store bounds for the finite composition selector. -/
namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem take_payload_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (((s 5).tail).takeWhile isPayload).length ≤ budget := by
  have tail : (s 5).tail.length ≤ budget := by
    simpa only [List.length_tail] using (Nat.sub_le (s 5).length 1).trans (sizes 5)
  exact (List.takeWhile_sublist (l := (s 5).tail) isPayload).length_le.trans tail

/-- Reading an entry moves its payload, rather than copying the archive. -/
theorem readEntry_bound {O : Type} (s : Store) (budget : ℕ)
    (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((readEntry (O := O)).eval s) budget ∧
      (readEntry (O := O)).cost s ≤ 40*(budget+1) := by
  have taken := take_payload_bound s budget sizes
  have tail : (s 5).tail.length ≤ budget := by
    simpa only [List.length_tail] using (Nat.sub_le (s 5).length 1).trans (sizes 5)
  have dropped : (((s 5).tail).dropWhile isPayload).length ≤ budget :=
    (List.dropWhile_sublist (l := (s 5).tail) isPayload).length_le.trans tail
  constructor
  · intro j
    by_cases a : j = 5 <;> by_cases b : j = 7 <;> by_cases c : j = 8 <;> by_cases d : j = 9 <;>
      simp [readEntry,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.branch,
        WordStack.Routine.ofLocal,Local.eval_pop,Local.eval_push,WordStack.Routine.skip,
        WordStack.Routine.transferWhile,WordStack.Routine.transfer,a,b,c,d] <;>
      split_ifs <;> simp_all <;> exact sizes j
  · have s7 := sizes 7
    have s8 := sizes 8
    have s9 := sizes 9
    simp [readEntry,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.branch,
      WordStack.Routine.ofLocal,Local.pop,Local.push,Local.ticks,Local.eval_pop,Local.eval_push,
      WordStack.Routine.skip,Local.eval,Action.apply,WordStack.Routine.transferWhile,WordStack.Routine.transfer]
    split_ifs <;> simp_all <;> omega

/-- Capturing a predecessor adds only its positive unary part and one marker. -/
theorem capture_bound {O : Type} (s : Store) (budget extra : ℕ)
    (sizes : StoreBound s budget) (counter : (s 3).length ≤ extra) (empty : s 11 = []) :
    StoreBound ((capture (O := O)).eval s) (budget+extra+1) ∧
      (capture (O := O)).cost s ≤ 60*(budget+1) := by
  constructor
  · rw [capture_eval]
    apply ((sizes.mono (by omega)).clear 12).update 10 _ ?_ |>.update 11 _ ?_
    · simp only [List.length_cons,List.length_append,List.length_replicate]
      have := sizes 8
      omega
    · simp [empty]
  · have s3 := sizes 3
    have s8 := sizes 8
    have s10 := sizes 10
    have s12 := sizes 12
    simp [capture,WordStack.Routine.seq,WordStack.Routine.assign_cost,WordStack.Routine.assign_eval,
      WordStack.Routine.copy,WordStack.Routine.ofLocal,Local.push,Local.ticks]
    omega

theorem consider_bound {O : Type} (s : Store) (budget extra : ℕ)
    (sizes : StoreBound s budget) (counter : (s 3).length ≤ extra) :
    StoreBound ((consider (O := O)).eval s) (budget+extra+1) ∧
      (consider (O := O)).cost s ≤ 70*(budget+1) := by
  by_cases found : (s 11).head?.isSome = true
  · simp only [consider,WordStack.Routine.branch,found,Bool.false_eq_true,ite_true,ite_false]
    exact ⟨sizes.mono (by omega),by
      simp only [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.ticks]
      omega⟩
  · by_cases flag : available (s 6).head? = true
    · by_cases previous : (s 9).head?.isSome = true
      · have empty : s 11 = [] := by
          cases word : s 11 with
          | nil => rfl
          | cons letter rest => simp [word] at found
        have captured := capture_bound (O := O) s budget extra sizes counter empty
        simp only [consider,WordStack.Routine.branch,found,flag,previous,Bool.false_eq_true,ite_false,ite_true]
        exact ⟨captured.1,by omega⟩
      · simp only [consider,WordStack.Routine.branch,found,flag,previous,Bool.false_eq_true,ite_false,ite_true]
        exact ⟨sizes.mono (by omega),by
          simp only [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.ticks]
          omega⟩
    · simp only [consider,WordStack.Routine.branch,found,flag,Bool.false_eq_true,ite_false]
      exact ⟨sizes.mono (by omega),by
        simp only [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.ticks]
        omega⟩

end ComplexityOfGenerators.Simulation.StarPaths
