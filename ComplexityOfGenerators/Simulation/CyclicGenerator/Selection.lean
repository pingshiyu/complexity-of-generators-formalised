import ComplexityOfGenerators.Simulation.CyclicGenerator.Output
import ComplexityOfGenerators.Simulation.CyclicGenerator.Restart

/-! The fair selection coin after an accepting decision. False selects the
word; true continues enumeration and records that this pass was nonempty. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem accepting_instruction (word : List α) (seen : Bool) (random : ℕ)
    (source : Configuration D)
    (accepts : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .accept) :
    (bank D).instruction (generatorData word.length) (decisionConfig D word seen random source) =
      .readRandom .outputOrigin (.eraseLeft true) := by
  simp [TransducerBank.TapeBank.instruction, decisionConfig, bank, select, transition, accepts]

theorem select_word (word : List α) (seen : Bool) (random : ℕ) (bits : BitString)
    (source : Configuration D)
    (accepts : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .accept) (coin : bits[random]? = some false) :
    (bank D).Executes (generatorData word.length) bits (decisionConfig D word seen random source)
      (source.inputHead + 1 + word.length + 1) (.accepted word) := by
  let c := decisionConfig D word seen random source
  let d := TransducerBank.TapeBank.choose c (Phase.outputOrigin : State D)
  have output := output_executes D word bits d rfl (by simp [d, c, decisionConfig,
    TransducerBank.TapeBank.choose]) source.inputHead (by simp [d, c, decisionConfig,
    TransducerBank.TapeBank.choose]) rfl rfl le_rfl
  have step := TransducerBank.TapeBank.Executes.random (B := bank D)
    c .outputOrigin (.eraseLeft true) false _ (.accepted word)
      (accepting_instruction D word seen random source accepts) coin
      (by simpa [d, c, decisionConfig, TransducerBank.TapeBank.choose] using output)
  exact step

theorem decline_word (word : List α) (seen : Bool) (random : ℕ) (bits : BitString)
    (source : Configuration D)
    (accepts : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .accept) (coin : bits[random]? = some true) :
    (bank D).Steps (generatorData word.length) bits (decisionConfig D word seen random source) 1
      {decisionConfig D word true (random + 1) source with state := .eraseLeft true} := by
  exact .random _ .outputOrigin (.eraseLeft true) true 0 _
    (accepting_instruction D word seen random source accepts) coin (.refl _)

theorem reject_word (word : List α) (seen : Bool) (random : ℕ) (bits : BitString)
    (source : Configuration D)
    (rejects : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .reject) :
    (bank D).Steps (generatorData word.length) bits (decisionConfig D word seen random source) 1
      {decisionConfig D word seen random source with state := .eraseLeft seen} := by
  apply TransducerBank.TapeBank.Steps.go
  · simp [decisionConfig, generatorData]
  · simp [decisionConfig, generatorData]
  · simp [decisionConfig, generatorData]
  · simp [TransducerBank.TapeBank.instruction, decisionConfig, bank, select, transition, rejects]

theorem selection_exhausted (word : List α) (seen : Bool) (random : ℕ) (bits : BitString)
    (source : Configuration D)
    (accepts : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .accept) (absent : bits[random]? = none) :
    (bank D).Executes (generatorData word.length) bits (decisionConfig D word seen random source)
      0 .exhausted :=
  .exhausted _ .outputOrigin (.eraseLeft true)
    (accepting_instruction D word seen random source accepts) absent

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
