import ComplexityOfGenerators.Simulation.CompositionMemory

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

/-- Read the virtual index and certificate cells before the recoverer's work
instruction; the sampled certificate is never copied into finite control. -/
theorem composition_recoverer_fetch (n : ℕ) (certificate bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (c : Configuration R) :
    (samplerCompositionBank S R).Steps (generatorData n) bits
      (recovererBankConfiguration S R n certificate samplerWork samplerHead c) 2
      {recovererBankConfiguration S R n certificate samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) certificate[c.auxiliaryHead]?} := by
  let B := samplerCompositionBank S R
  let start := recovererBankConfiguration S R n certificate samplerWork samplerHead c
  let middle : CompositionConfiguration S R := {start with state := CompositionPhase.recoverAux c.state (decide (c.indexHead < n))}
  have first : B.Steps (generatorData n) bits start 1 middle := by
    apply TransducerBank.TapeBank.Steps.go <;>
      simp [B, start, TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
        compositionSelect, compositionTransition, compositionIndex, generatorData]
  have second : B.Steps (generatorData n) bits middle 1
      {start with state := .recoverWork c.state (decide (c.indexHead < n)) certificate[c.auxiliaryHead]?} := by
    apply TransducerBank.TapeBank.Steps.go <;>
      simp [B, middle, start, TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
        compositionSelect, compositionTransition, generatorData]
  exact first.trans B second

/-- Update the three independent simulated tapes and emit at most one letter. -/
theorem composition_recoverer_step (n : ℕ) (certificate bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (c : Configuration R)
    (indexBound : c.indexHead ≤ n) (auxiliaryBound : c.auxiliaryHead ≤ certificate.length)
    (next : Fin R.states) (write : Option (Fin R.symbols)) (work input auxiliary index : Move) (emit : Option α)
    (action : R.transition c.state none certificate[c.auxiliaryHead]?
      (if c.indexHead < n then some () else none) (c.work c.workHead) =
      .step next write work input auxiliary index emit) :
    (samplerCompositionBank S R).Steps (generatorData n) bits
      {recovererBankConfiguration S R n certificate samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) certificate[c.auxiliaryHead]?} 3
      (recovererBankConfiguration S R n certificate samplerWork samplerHead
        (R.stepConfiguration (generatorData n certificate) c next write work input auxiliary index emit)) := by
  let B := samplerCompositionBank S R
  let c₀ : CompositionConfiguration S R :=
    {recovererBankConfiguration S R n certificate samplerWork samplerHead c with
      state := .recoverWork c.state (decide (c.indexHead < n)) certificate[c.auxiliaryHead]?}
  let written : CompositionSymbol S R := {recoverer := match write with | none => c.work c.workHead | some a => some a}
  let c₁ := B.advance (generatorData n) c₀ (.recoverIndex next index auxiliary) written work .stay .stay .stay emit
  have first : B.Steps (generatorData n) bits c₀ 1 c₁ := by
    apply TransducerBank.TapeBank.Steps.single
    cases write <;> simp [B, c₀, TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
      compositionSelect, compositionTransition, action, written]
  let indexMove := clampedReadMove (decide ((c.indexHead : ℤ) = 0)) (decide (c.indexHead < n)) index
  have indexMoved : indexMove.onInt c.indexHead = ((index.onInput n c.indexHead : ℕ) : ℤ) :=
    clampedReadMove_correct n c.indexHead indexBound index
  let c₂ := B.advance (generatorData n) c₁ (.recoverAuxMove next auxiliary)
    (compositionIndex S R n c.indexHead) indexMove .stay .stay .stay none
  have second : B.Steps (generatorData n) bits c₁ 1 c₂ := by
    apply TransducerBank.TapeBank.Steps.single
    simp [B, c₁, c₀, TransducerBank.TapeBank.instruction, TransducerBank.TapeBank.advance,
      samplerCompositionBank, recovererBankConfiguration, compositionSelect, compositionTransition, compositionIndex, indexMove]
  let auxiliaryMove := clampedReadMove (decide ((c.auxiliaryHead : ℤ) = 0)) (decide (c.auxiliaryHead < certificate.length)) auxiliary
  have auxiliaryMoved : auxiliaryMove.onInt c.auxiliaryHead = ((auxiliary.onInput certificate.length c.auxiliaryHead : ℕ) : ℤ) :=
    clampedReadMove_correct certificate.length c.auxiliaryHead auxiliaryBound auxiliary
  have live : (certificate[c.auxiliaryHead]?).isSome = decide (c.auxiliaryHead < certificate.length) := by
    by_cases inside : c.auxiliaryHead < certificate.length
    · simp [List.getElem?_eq_getElem inside, inside]
    · simp [List.getElem?_eq_none (by omega : certificate.length ≤ c.auxiliaryHead), inside]
  let c₃ := B.advance (generatorData n) c₂ (.recover next)
    (compositionCertificate S R certificate c.auxiliaryHead) auxiliaryMove .stay .stay .stay none
  have third : B.Steps (generatorData n) bits c₂ 1 c₃ := by
    apply TransducerBank.TapeBank.Steps.single
    simp [B, c₂, c₁, c₀, TransducerBank.TapeBank.instruction, TransducerBank.TapeBank.advance,
      samplerCompositionBank, recovererBankConfiguration, compositionSelect, compositionTransition, auxiliaryMove, live]
  have equal : c₃ = recovererBankConfiguration S R n certificate samplerWork samplerHead
      (R.stepConfiguration (generatorData n certificate) c next write work input auxiliary index emit) := by
    apply TransducerBank.BankConfiguration.ext
    · rfl
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, recovererBankConfiguration, Move.onInput, generatorData]
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, recovererBankConfiguration, Move.onInput, generatorData]
    · simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, recovererBankConfiguration, Move.onInput, generatorData]
    · rfl
    · cases emit <;> simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, recovererBankConfiguration, Machine.stepConfiguration]
    · funext j
      fin_cases j <;>
        simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, samplerCompositionBank, compositionSelect,
          recovererBankConfiguration, Machine.stepConfiguration, generatorData, Move.onInt]
      all_goals first | exact indexMoved | exact auxiliaryMoved
    · funext j i
      fin_cases j <;> cases write <;>
        simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, samplerCompositionBank, compositionSelect,
          recovererBankConfiguration, Machine.stepConfiguration, written, Function.update_apply]
      all_goals first | (split_ifs <;> simp_all) | simp_all
  rw [← equal]
  exact (first.trans B second).trans B third

theorem composition_recoverer_random (n : ℕ) (certificate bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (c : Configuration R)
    (no yes : Fin R.states) (bit : Bool)
    (action : R.transition c.state none certificate[c.auxiliaryHead]?
      (if c.indexHead < n then some () else none) (c.work c.workHead) = .readRandom no yes)
    (lookup : bits[c.randomHead]? = some bit) :
    (samplerCompositionBank S R).Steps (generatorData n) bits
      {recovererBankConfiguration S R n certificate samplerWork samplerHead c with
        state := .recoverWork c.state (decide (c.indexHead < n)) certificate[c.auxiliaryHead]?} 1
      (recovererBankConfiguration S R n certificate samplerWork samplerHead
        {c with state := if bit then yes else no, randomHead := c.randomHead + 1}) := by
  apply TransducerBank.TapeBank.Steps.random _ (.recover no) (.recover yes) bit 0 _
  · simp [TransducerBank.TapeBank.instruction, samplerCompositionBank, recovererBankConfiguration,
      compositionSelect, compositionTransition, action]
  · exact lookup
  · cases bit <;> exact .refl _

end
end ComplexityOfGenerators.Simulation
