import ComplexityOfGenerators.Simulation.CompositionMemory

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

open TransducerBank

/-- Read the simulated unary-index cell before looking up a sampler instruction. -/
theorem composition_sampler_fetch (n : ℕ) (bits : BitString) (c : Configuration S) :
    (samplerCompositionBank S R).Steps (generatorData n) bits (samplerBankConfiguration S R n c) 1
      {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))} := by
  apply TransducerBank.TapeBank.Steps.go <;>
    simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, samplerBankConfiguration,
      compositionSelect, compositionTransition, compositionIndex, generatorData]

/-- The three operations following fetch update sampler work, index and the
certificate buffer. Their order introduces no whole-word primitive. -/
theorem composition_sampler_step (n : ℕ) (bits : BitString) (c : Configuration S)
    (indexBound : c.indexHead ≤ n)
    (next : Fin S.states) (write : Option (Fin S.symbols)) (work input auxiliary index : Move) (emit : Option Bool)
    (action : S.transition c.state none none (if c.indexHead < n then some () else none) (c.work c.workHead) =
      .step next write work input auxiliary index emit) :
    (samplerCompositionBank S R).Steps (generatorData n) bits
      {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))} 3
      (samplerBankConfiguration S R n (S.stepConfiguration (generatorData n) c next write work input auxiliary index emit)) := by
  let B := samplerCompositionBank S R
  let c₀ : CompositionConfiguration S R :=
    {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))}
  let written : CompositionSymbol S R := {sampler := match write with | none => c.work c.workHead | some a => some a}
  let c₁ := B.advance (generatorData n) c₀ (.sampleIndex next index emit) written work .stay .stay .stay none
  have first : B.Steps (generatorData n) bits c₀ 1 c₁ := by
    apply TransducerBank.TapeBank.Steps.single
    cases write <;> simp [B, c₀, TransducerBank.TapeBank.instruction, samplerCompositionBank, samplerBankConfiguration,
      compositionSelect, compositionTransition, action, written]
  let move := clampedReadMove (decide ((c.indexHead : ℤ) = 0)) (decide (c.indexHead < n)) index
  have moved : move.onInt c.indexHead = ((index.onInput n c.indexHead : ℕ) : ℤ) :=
    clampedReadMove_correct n c.indexHead indexBound index
  let c₂ := B.advance (generatorData n) c₁ (.sampleEmit next emit)
    (compositionIndex S R n c.indexHead) move .stay .stay .stay none
  have second : B.Steps (generatorData n) bits c₁ 1 c₂ := by
    apply TransducerBank.TapeBank.Steps.single
    simp [B, c₁, c₀, TransducerBank.TapeBank.instruction, TransducerBank.TapeBank.advance, samplerCompositionBank, samplerBankConfiguration,
      compositionSelect, compositionTransition, compositionIndex, move]
  let emitted : CompositionSymbol S R := match emit with | none => {} | some bit => {certificate := some bit}
  let outMove := match emit with | none => Move.stay | some _ => Move.right
  let c₃ := B.advance (generatorData n) c₂ (.sample next) emitted outMove .stay .stay .stay none
  have third : B.Steps (generatorData n) bits c₂ 1 c₃ := by
    apply TransducerBank.TapeBank.Steps.single
    cases emit <;>
      simp [B, c₂, c₁, c₀, TransducerBank.TapeBank.instruction, TransducerBank.TapeBank.advance, samplerCompositionBank, samplerBankConfiguration,
        compositionSelect, compositionTransition, emitted, outMove]
  have equal : c₃ = samplerBankConfiguration S R n
      (S.stepConfiguration (generatorData n) c next write work input auxiliary index emit) := by
    apply TransducerBank.BankConfiguration.ext
    · rfl
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, samplerBankConfiguration, Move.onInput, generatorData]
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, samplerBankConfiguration, Move.onInput, generatorData]
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, samplerBankConfiguration, Move.onInput, generatorData]
    · rfl
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, samplerBankConfiguration, Machine.stepConfiguration]
    · funext j
      fin_cases j <;> cases emit <;>
        simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, samplerCompositionBank, compositionSelect,
          samplerBankConfiguration, Machine.stepConfiguration, generatorData, Move.onInt, outMove]
      all_goals exact moved
    · funext j i
      fin_cases j <;> cases emit <;> cases write <;>
        simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, samplerCompositionBank, compositionSelect,
          samplerBankConfiguration, Machine.stepConfiguration, written, emitted,
          ← compositionCertificate_append S R, Function.update_apply]
      all_goals first | (split_ifs <;> simp_all) | simp_all
  rw [← equal]
  exact (first.trans B second).trans B third

/-- Random choices update just finite control and the shared random cursor. -/
theorem composition_sampler_random (n : ℕ) (bits : BitString) (c : Configuration S)
    (no yes : Fin S.states) (bit : Bool)
    (action : S.transition c.state none none (if c.indexHead < n then some () else none) (c.work c.workHead) = .readRandom no yes)
    (lookup : bits[c.randomHead]? = some bit) :
    (samplerCompositionBank S R).Steps (generatorData n) bits
      {samplerBankConfiguration S R n c with state := .sampleWork c.state (decide (c.indexHead < n))} 1
      (samplerBankConfiguration S R n {c with state := if bit then yes else no, randomHead := c.randomHead + 1}) := by
  apply TransducerBank.TapeBank.Steps.random _ (.sample no) (.sample yes) bit 0 _
  · simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, samplerBankConfiguration,
      compositionSelect, compositionTransition, action]
  · exact lookup
  · cases bit <;> exact .refl _

end
end ComplexityOfGenerators.Simulation
