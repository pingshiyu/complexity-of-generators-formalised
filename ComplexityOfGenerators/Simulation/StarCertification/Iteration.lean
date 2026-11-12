import ComplexityOfGenerators.Simulation.StarCertification.Body

namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] body scan prepare finish routine

private theorem stored_pop (start : ℕ) (prior : List Bool) (bits : BitString) (s : Store M)
    (stored : Stored M start prior bits s) :
    Stored M start prior bits (Function.update s 23 (s 23).tail) := by
  constructor
  · simpa using stored.counter
  · simpa using stored.random
  · simpa using stored.cache

/-- The actual counted controller runs the source tests in ascending order,
using disjoint consecutive slices of the supplied block. -/
theorem counted_walk (p : PolynomialBound) (start count : ℕ) (prior : List Bool) (bits : BitString) (s : Store M)
    (stored : Stored M start prior bits s) :
    Stored M (start+count) ((walk M p start count bits).1.reverse++prior) (walk M p start count bits).2
      ((WordStack.Routine.counted 23 (body M p)).eval^[count] s) := by
  induction count generalizing start prior bits s with
  | zero => simpa [walk] using stored
  | succ count ih =>
      let ready := (WordStack.Routine.counted 23 (body M p)).eval s
      have first := body_stored M p start prior bits (Function.update s 23 (s 23).tail) (stored_pop M start prior bits s stored)
      have next := ih (start+1) (testFlag M p (start+1) bits::prior)
        (bits.drop (IndexwiseCertification.seed p (start+1))) ready first
      simpa only [Function.iterate_succ_apply,walk,List.reverse_cons,List.append_assoc,List.singleton_append,
        Nat.add_assoc,Nat.add_comm 1 count] using next

theorem prepare_fields (s : Store M) (bits : BitString) (coins : s 17 = bits.map (bitSymbol M)) :
    Stored M 0 [] bits ((prepare M).eval s) ∧ ((prepare M).eval s 23).length = (s 22).length := by
  constructor
  · constructor <;> simp [prepare,WordStack.Routine.seq,WordStack.Routine.clear,
      WordStack.Routine.assign_eval,cacheWord,coins]
  · simp [prepare,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.assign_eval]

theorem finish_cache (s : Store M) : (finish M).eval s 25 = (s 25).reverse := by
  simp [finish,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.transfer,WordStack.Routine.assign_eval]

theorem prepare_frame (j : Fin 35) (a : j ≠ 23) (b : j ≠ 24) (c : j ≠ 25) (d : j ≠ 33) :
    (prepare M).Fixes j := by
  intro s
  simp [prepare,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.assign_eval,a,b,c,d]

theorem finish_frame (j : Fin 35) (a : j ≠ 25) (b : j ≠ 33) (c : j ≠ 34) : (finish M).Fixes j := by
  intro s
  simp [finish,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.transfer,
    WordStack.Routine.assign_eval,a,b,c]

/-- End-to-end native certification semantics, including arbitrary initial
cache data, zero's empty scan, and the exact unused suffix of the coin list. -/
theorem routine_value (p : PolynomialBound) (s : Store M) (bits : BitString)
    (coins : s 17 = bits.map (bitSymbol M)) :
    (routine M p).eval s 25 = cacheWord M (walk M p 0 (s 22).length bits).1 ∧
      (routine M p).eval s 17 = (walk M p 0 (s 22).length bits).2.map (bitSymbol M) := by
  let prepared := (prepare M).eval s
  let tested := (scan M p).eval prepared
  have initial := prepare_fields M s bits coins
  have result := counted_walk M p 0 (s 22).length [] bits prepared initial.1
  have actualScan : tested = ((WordStack.Routine.counted 23 (body M p)).eval^[(s 22).length]) prepared := by
    unfold tested scan
    change ((WordStack.Routine.counted 23 (body M p)).eval^[(prepared 23).length]) prepared = _
    rw [initial.2]
  have testedCache : tested 25 = cacheWord M (walk M p 0 (s 22).length bits).1.reverse := by
    rw [actualScan]
    simpa only [List.append_nil] using result.cache
  have testedRandom : tested 17 = (walk M p 0 (s 22).length bits).2.map (bitSymbol M) := by
    rw [actualScan]
    exact result.random
  have actual : (routine M p).eval s = (finish M).eval tested := by unfold routine; rfl
  rw [actual]
  constructor
  · rw [finish_cache,testedCache]
    simp [cacheWord,List.map_reverse]
  · exact (finish_frame M 17 (by decide) (by decide) (by decide) tested).trans testedRandom

theorem routine_frame (p : PolynomialBound) (j : Fin 35) (upper : 22 ≤ j.val)
    (a : j ≠ 23) (b : j ≠ 24) (c : j ≠ 25) (d : j ≠ 33) (e : j ≠ 34) :
    (routine M p).Fixes j := by
  unfold routine scan
  exact (prepare_frame M j a b c d).seq
    ((WordStack.Routine.Fixes.iterate 23 (body M p) (body_frame M p 23 (by decide) (by decide) (by decide))
      j a (body_frame M p j upper b c)).seq (finish_frame M j c d e))

end ComplexityOfGenerators.Simulation.StarCertification
