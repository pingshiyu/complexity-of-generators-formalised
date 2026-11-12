import ComplexityOfGenerators.Simulation.StarCertification.Body
import ComplexityOfGenerators.Simulation.StarCertification.Blocks

namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] bodyPrefix trial record body

/-- Safe initialization of the next source call, including arbitrary old
source input and scratch data. -/
theorem bodyPrefix_bound (s : Store M) (cap : ℕ) (sizes : StoreBound s cap)
    (fresh : (s 24).length+1 ≤ cap) :
    StoreBound ((bodyPrefix M).eval s) cap ∧ (bodyPrefix M).cost s ≤ 40*(cap+1) := by
  let pushed := Function.update s 24 (unit M::s 24)
  let assigned := (WordStack.Routine.assign (O := α) 24 13 15 (by decide) (by decide) (by decide) id).eval pushed
  have pushedBound : StoreBound pushed cap := sizes.update 24 _ (by simpa using fresh)
  have assignedBound : StoreBound assigned cap := pushedBound.assign (O := α) 24 13 15 (by decide) (by decide) (by decide) id
  have assignedCost : (WordStack.Routine.assign (O := α) 24 13 15 (by decide) (by decide) (by decide) id).cost pushed ≤ 20*cap+3 := by
    have a := pushedBound 13
    have b := pushedBound 15
    have c := pushedBound 24
    simp only [WordStack.Routine.assign_cost]
    omega
  have clearCost : (WordStack.Routine.clearMany (S := Cell M) (O := α) [11,12,14]).cost assigned ≤ 10*cap+5 := by
    have a := assignedBound 11
    have b := assignedBound 12
    have c := assignedBound 14
    simp [WordStack.Routine.clearMany,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.skip,
      WordStack.Routine.ofLocal,Local.ticks]
    omega
  constructor
  · unfold bodyPrefix
    exact assignedBound.clearMany (O := α) [11,12,14]
  · unfold bodyPrefix
    change 1+1+((WordStack.Routine.assign (O := α) 24 13 15 _ _ _ id).cost pushed+1+
      (WordStack.Routine.clearMany (O := α) [11,12,14]).cost assigned) ≤ _
    omega

theorem record_bound (s : Store M) (cap : ℕ) (sizes : StoreBound s cap)
    (fresh : (s 25).length+1 ≤ cap) :
    StoreBound ((record M).eval s) cap ∧ (record M).cost s ≤ 2 := by
  constructor
  · unfold record
    change StoreBound (Function.update s 25 (flagSymbol M (accepted M (s 0).head?)::s 25)) cap
    exact sizes.update 25 _ (by simpa using fresh)
  · simp [record,WordStack.Routine.branch,WordStack.Routine.ofLocal,Local.push,Local.ticks]

noncomputable def stepBudget (p : PolynomialBound) (n cap : ℕ) : ℕ :=
  ((Source.body M (encode M) (decode M) (Source.bank BoundedSource.sourceSlots)).bound+500)*(cap+1)+
    Command.counterBudget (IndexwiseCertification.seed p) n+
    Command.counterBudget (IndexwiseCertification.clock p) n

/-- Uniform bounds for the actual finite capped test. Source expected time
is not an assumption here: the native test uses a fixed clock. -/
theorem body_bound (p : PolynomialBound) (start n cap : ℕ) (prior : List Bool) (bits : BitString) (s : Store M)
    (stored : Stored M start prior bits s) (priorBound : prior.length ≤ start) (indexBound : start < n)
    (sizes : StoreBound s cap) (base : n+1 ≤ cap)
    (seedBound : IndexwiseCertification.seed p n ≤ cap) (timeBound : IndexwiseCertification.clock p n+1 ≤ cap)
    (space : 1+n+IndexwiseCertification.seed p n+3*(IndexwiseCertification.clock p n+1) ≤ cap) :
    StoreBound ((body M p).eval s) cap ∧ (body M p).cost s ≤ stepBudget M p n cap := by
  let prepared := (bodyPrefix M).eval s
  let tested := (trial M p).eval prepared
  obtain ⟨preparedBound,preparedCost⟩ := bodyPrefix_bound M s cap sizes (by rw [stored.counter,List.length_replicate]; omega)
  have preparedInput : prepared 11 = [] := by simp [prepared,bodyPrefix,WordStack.Routine.seq,WordStack.Routine.ofLocal,
    Local.eval_push,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]
  have preparedAuxiliary : prepared 12 = [] := by simp [prepared,bodyPrefix,WordStack.Routine.seq,WordStack.Routine.ofLocal,
    Local.eval_push,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]
  have preparedEmpty : prepared 14 = [] := by simp [prepared,bodyPrefix,WordStack.Routine.seq,WordStack.Routine.ofLocal,
    Local.eval_push,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]
  have preparedIndex : (prepared 13).length = start+1 := by simp [prepared,bodyPrefix,WordStack.Routine.seq,WordStack.Routine.ofLocal,
    Local.eval_push,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval,stored.counter]
  have preparedRandom : prepared 17 = bits.map (bitSymbol M) :=
    (bodyPrefix_frame M 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s).trans stored.random
  have index : start+1 ≤ n := by omega
  have seeds := (IndexwiseCertification.seed p).monotone index
  have times := (IndexwiseCertification.clock p).monotone index
  obtain ⟨testedBound,_,testedCost⟩ := BoundedSource.sourceTrial_bound (O := α) (unit M) (bitSymbol M) M (encode M) (decode M)
    (decode_encode M) (fun _ => encode M .unit) (fun _ => encode M .unit) (bitMap M) (bitMap_bit M)
    (IndexwiseCertification.seed p) (IndexwiseCertification.clock p) prepared (generatorData (start+1)) bits
    (by simp [preparedInput,generatorData]) (by simp [preparedAuxiliary,generatorData]) preparedIndex preparedRandom preparedEmpty
    cap preparedBound (by simpa [generatorData] using (by omega : start+1+1 ≤ cap))
    (by simpa [generatorData] using seeds.trans seedBound) (by simpa [generatorData] using (by omega : IndexwiseCertification.clock p (start+1)+1 ≤ cap))
    (by simpa [generatorData] using (by omega : 1+(start+1)+IndexwiseCertification.seed p (start+1)+3*(IndexwiseCertification.clock p (start+1)+1) ≤ cap))
  have actualSize : StoreBound tested cap := by
    dsimp only [tested]
    simpa only [trial] using testedBound
  have cache : tested 25 = cacheWord M prior :=
    (trial_frame M p 25 (by decide) prepared).trans
      ((bodyPrefix_frame M 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s).trans stored.cache)
  obtain ⟨recordSize,recordCost⟩ := record_bound M tested cap actualSize (by rw [cache]; simp only [cacheWord,List.length_map]; omega)
  constructor
  · unfold body
    exact recordSize
  · have sourceCost : (trial M p).cost prepared ≤
        ((Source.body M (encode M) (decode M) (Source.bank BoundedSource.sourceSlots)).bound+200)*(cap+1)+
          Command.counterBudget (IndexwiseCertification.seed p) (start+1)+
          Command.counterBudget (IndexwiseCertification.clock p) (start+1) := by
      simpa only [trial,generatorData] using testedCost
    have seedCost := (Command.counterBudget (IndexwiseCertification.seed p)).monotone index
    have timeCost := (Command.counterBudget (IndexwiseCertification.clock p)).monotone index
    unfold body
    change (bodyPrefix M).cost s+1+((trial M p).cost prepared+1+(record M).cost tested) ≤ _
    unfold stepBudget
    simp only [Nat.add_mul,Nat.mul_add] at sourceCost ⊢
    omega

end ComplexityOfGenerators.Simulation.StarCertification
