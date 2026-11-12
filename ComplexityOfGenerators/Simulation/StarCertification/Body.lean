import ComplexityOfGenerators.Simulation.StarCertification.Model

namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] trial bodyPrefix record body

structure Stored (start : ℕ) (prior : List Bool) (bits : BitString) (s : Store M) : Prop where
  counter : s 24 = List.replicate start (unit M)
  random : s 17 = bits.map (bitSymbol M)
  cache : s 25 = cacheWord M prior

private theorem prefix_fields (s : Store M) :
    (bodyPrefix M).eval s 24 = unit M::s 24 ∧
      ((bodyPrefix M).eval s 13).length = (s 24).length+1 ∧
      (bodyPrefix M).eval s 11 = [] ∧ (bodyPrefix M).eval s 12 = [] ∧ (bodyPrefix M).eval s 14 = [] := by
  simp [bodyPrefix,WordStack.Routine.seq,WordStack.Routine.ofLocal,Local.eval_push,
    WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]

private theorem record_value (s : Store M) :
    (record M).eval s 25 = flagSymbol M (accepted M (s 0).head?)::s 25 := by
  simp [record,WordStack.Routine.branch,WordStack.Routine.ofLocal,Local.eval_push]

/-- One actual bounded native source run records exactly its acceptance
flag and consumes exactly its assigned finite block. -/
theorem body_stored (p : PolynomialBound) (start : ℕ) (prior : List Bool) (bits : BitString) (s : Store M)
    (stored : Stored M start prior bits s) :
    Stored M (start+1) (testFlag M p (start+1) bits::prior)
      (bits.drop (IndexwiseCertification.seed p (start+1))) ((body M p).eval s) := by
  let prepared := (bodyPrefix M).eval s
  let tested := (trial M p).eval prepared
  have fields := prefix_fields M s
  have emptyInput : prepared 11 = [] := fields.2.2.1
  have emptyAuxiliary : prepared 12 = [] := fields.2.2.2.1
  have emptyRandom : prepared 14 = [] := fields.2.2.2.2
  have preparedCounter : prepared 24 = unit M::s 24 := fields.1
  have index : (prepared 13).length = start+1 := by
    rw [fields.2.1,stored.counter,List.length_replicate]
  have random : prepared 17 = bits.map (bitSymbol M) :=
    (bodyPrefix_frame M 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s).trans stored.random
  have input : (prepared 11).map (fun _ => encode M Source.Cell.unit) =
      (generatorData (start+1)).input.map (fun a => encode M (.input a)) := by simp [emptyInput,generatorData]
  have auxiliary : (prepared 12).map (fun _ => encode M Source.Cell.unit) =
      (generatorData (start+1)).auxiliary.map (fun a => encode M (.auxiliary a)) := by simp [emptyAuxiliary,generatorData]
  obtain ⟨status,output,state,_,native⟩ := BoundedSource.sourceTrial_result (O := α)
    (unit M) (bitSymbol M) M (encode M) (decode M) (decode_encode M)
    (fun _ => encode M .unit) (fun _ => encode M .unit) (bitMap M) (bitMap_bit M)
    (IndexwiseCertification.seed p) (IndexwiseCertification.clock p) prepared (generatorData (start+1)) bits
    input auxiliary index random emptyRandom
  have outside (j : Fin 35) (large : 11 ≤ j.val) (clock : j ≠ 16) :=
    BoundedSource.sourceTrial_outside (O := α) (unit M) (bitSymbol M) M (encode M) (decode M)
      (fun _ => encode M .unit) (fun _ => encode M .unit) (bitMap M)
      (IndexwiseCertification.seed p) (IndexwiseCertification.clock p) prepared j large clock
  have testedRandom : tested 17 = (bits.drop (IndexwiseCertification.seed p (start+1))).map (bitSymbol M) := by
    simpa [tested,trial,BoundedSource.trialPrepared,random,index,List.map_drop] using outside 17 (by decide) (by decide)
  have testedCounter : tested 24 = List.replicate (start+1) (unit M) := by
    have frame := trial_frame M p 24 (by decide) prepared
    change tested 24 = prepared 24 at frame
    rw [frame,preparedCounter,stored.counter,List.replicate_succ]
  have testedCache : tested 25 = cacheWord M prior :=
    (trial_frame M p 25 (by decide) prepared).trans
      ((bodyPrefix_frame M 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s).trans stored.cache)
  have nativeResult (word : List α) : (status = .accepted ∧ output.reverse = word) ↔
      M.run (generatorData (start+1)) (bits.take (IndexwiseCertification.seed p (start+1)))
        (IndexwiseCertification.clock p (start+1)) = .halted (.accepted word) := by
    simpa only [generatorData] using native word
  have value : UnionGenerator.sourceValue M (IndexwiseCertification.clock p) (start+1)
      (bits.take (IndexwiseCertification.seed p (start+1))) =
      if status = .accepted then some output.reverse else none := by
    apply Option.ext
    intro word
    rw [UnionGenerator.sourceValue_eq_some,← nativeResult word]
    by_cases accepted : status = .accepted <;> simp [accepted]
  have testedState : tested 0 = [encode M (.state status)] := by
    dsimp only [tested]
    simpa only [trial] using state
  have flag : accepted M (tested 0).head? = testFlag M p (start+1) bits := by
    rw [testedState]
    unfold testFlag
    rw [value]
    cases status <;> rfl
  have actual : (body M p).eval s = (record M).eval tested := by unfold body; rfl
  rw [actual]
  constructor
  · exact (record_frame M 24 (by decide) tested).trans testedCounter
  · exact (record_frame M 17 (by decide) tested).trans testedRandom
  · rw [record_value,flag,testedCache]
    rfl

end ComplexityOfGenerators.Simulation.StarCertification
