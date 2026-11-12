import ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher.Semantics
import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.Semantics
import ComplexityOfGenerators.Simulation.TransducerBank.AcceptedRandomTape

/-! An actual ordinary-input recognizer for outputs of a uniform indexed bank.
The two adapters are composed as real finite transition tables: stream output
comparison, then charged unary-length preparation. Only a supplied all-branch
source bound gives an all-branch decider bound; accepting bounds alone do not
silently clock unsuccessful executions. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.IndexedOutputRecognizer

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (M : MultitapeMachine Unit Bool α)

def indexedData (word : Word α) : InputData α Bool :=
  {input := word, index := word.length}

abbrev machine : MultitapeMachine α Bool Unit :=
  OrdinaryIndex.machine (OutputMatcher.machine M)

theorem accepts_word_iff (word : Word α) (bits : BitString)
    (source : M.Terminates (generatorData word.length)) :
    (machine M).Accepts (decisionData word) bits ↔
      M.Produces (generatorData word.length) bits word := by
  have prepared := OutputMatcher.terminates M (indexedData word) source
  have first := OrdinaryIndex.accepts_iff (OutputMatcher.machine M) (decisionData word) bits prepared
  have second := OutputMatcher.accepts_word_iff M (indexedData word) bits source
  exact first.trans second

/-- Complete primitive bank cost, with no quadratic compilation hidden inside. -/
theorem timeBound (word : Word α) (time : ℕ)
    (source : M.TimeBound (generatorData word.length) time) :
    (machine M).TimeBound (decisionData word) (2 * word.length + 3 * time + 3) :=
  OrdinaryIndex.timeBound (OutputMatcher.machine M) (decisionData word) time
    (OutputMatcher.timeBound M (indexedData word) time source)

theorem acceptingTimeBound (word : Word α)
    (source : M.Terminates (generatorData word.length)) (time : ℕ)
    (bounded : M.AcceptingTimeBound (generatorData word.length) time) :
    (machine M).AcceptingTimeBound (decisionData word) (2 * word.length + 3 * time + 3) :=
  OrdinaryIndex.acceptingTimeBound (OutputMatcher.machine M) (decisionData word)
    (OutputMatcher.terminates M (indexedData word) source) time
    (OutputMatcher.acceptingTimeBound M (indexedData word) source time bounded)

end
end ComplexityOfGenerators.Simulation.TransducerBank.IndexedOutputRecognizer
