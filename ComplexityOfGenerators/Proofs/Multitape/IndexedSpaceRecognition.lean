import ComplexityOfGenerators.Proofs.Multitape.SpaceRecognition
import ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher.Space
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.Semantics

namespace ComplexityOfGenerators.Multitape
open Simulation.TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

noncomputable def binaryIndexMachine (source : MultitapeMachine α Bool Unit) : MultitapeMachine α Bool Unit where
  inputFinite := source.inputFinite
  auxiliaryFinite := source.auxiliaryFinite
  outputFinite := source.outputFinite
  Control := BinaryIndex.Control source.Control
  Work := BinaryIndex.WorkSymbol source.Work
  controlFinite := inferInstance
  workFinite := inferInstance
  tapes := 1+source.tapes
  program := BinaryIndex.bank source.program

/-- A supplied unary generator index is replaced by actual logarithmic work
counters before the space-constructed configuration clock is applied. -/
theorem indexed_output_mem_nspace (language : Language α) (source : MultitapeMachine Unit Bool α)
    (workspace space : ℕ→ℕ) (constructible : SpaceConstructible space) (order : ResourceOrder workspace space)
    (logarithm : ResourceOrder (fun n=>Nat.clog 2 (n+1)) space)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n)
    (terminates : ∀ n,source.Terminates (generatorData n))
    (bounded : ∀ n,source.SpaceBound (generatorData n) (workspace n))
    (correct : ∀ word,(∃ bits,source.Produces (generatorData word.length) bits word) ↔ word∈language) :
    language∈NSPACE α space := by
  let matcher := OutputMatcher.machine source
  let indexed := binaryIndexMachine matcher
  let region := fun n=>max (workspace n) (2*Nat.clog 2 (n+1)+4)
  have matcherTermination (word : Word α) : matcher.Terminates (BinaryIndex.sourceData (decisionData word)) :=
    OutputMatcher.terminates source _ (terminates word.length)
  have matcherBound (word : Word α) : matcher.SpaceBound (BinaryIndex.sourceData (decisionData word)) (workspace word.length) :=
    OutputMatcher.spaceBound source _ _ (terminates word.length) (bounded word.length)
  have indexTermination (word : Word α) : indexed.Terminates (decisionData word) :=
    BinaryIndex.terminates matcher.program (decisionData word) (workspace word.length) (matcherBound word) (matcherTermination word)
  have indexBound (word : Word α) : indexed.SpaceBound (decisionData word) (region word.length) :=
    BinaryIndex.spaceBound matcher.program (decisionData word) (workspace word.length) (matcherBound word) (matcherTermination word)
  have regionOrder : ResourceOrder region space :=
    (order.with_logarithmic_setup_of_bounds logarithm positive 1 2 4).mono (fun n=>by dsimp [region];omega)
  apply ordinary_input_mem_nspace language indexed region space constructible regionOrder logarithm positive indexTermination indexBound
  intro word
  have correspondence : (∃ bits,indexed.Accepts (decisionData word) bits) ↔
      (∃ bits,matcher.Accepts (BinaryIndex.sourceData (decisionData word)) bits) := by
    apply exists_congr
    intro bits
    apply exists_congr
    intro output
    exact BinaryIndex.accepted_iff matcher.program (decisionData word) bits output (workspace word.length)
      (matcherBound word) (matcherTermination word bits)
  rw [correspondence]
  have matched : (∃ bits,matcher.Accepts (BinaryIndex.sourceData (decisionData word)) bits) ↔
      (∃ bits,source.Produces (generatorData word.length) bits word) :=
    exists_congr fun bits=>OutputMatcher.accepts_word_iff source _ bits (terminates word.length)
  exact matched.trans (correct word)

end
end ComplexityOfGenerators.Multitape
