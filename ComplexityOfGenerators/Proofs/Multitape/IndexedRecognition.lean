import ComplexityOfGenerators.Simulation.TransducerBank.IndexedOutputRecognizer
import ComplexityOfGenerators.Proofs.Multitape.ResourceOrder
import ComplexityOfGenerators.Proofs.Multitape.GeneratorLayers
import ComplexityOfGenerators.MultitapeSpaceClasses

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

/-- A concrete indexed output bank with all-branch time bounds supplies an
ordinary-input nondeterministic decider. This constructs both finite adapters;
it is not a clock-constructor interface assumed for the source machine. -/
theorem indexed_output_mem_ntime (language : Language α) (M : MultitapeMachine Unit Bool α)
    (runtime time : ℕ → ℕ) (order : ResourceOrder runtime time)
    (dominates : ∀ n, n ≤ time n)
    (bounded : ∀ n, M.TimeBound (generatorData n) (runtime n))
    (coverage : ∀ word, (∃ bits, M.Produces (generatorData word.length) bits word) ↔ word ∈ language) :
    language ∈ NTIME α time := by
  have positive : ∃ threshold, ∀ n, threshold ≤ n → 1 ≤ time n :=
    ⟨1, fun n large => large.trans (dominates n)⟩
  have scan : ResourceOrder (fun n => 2 * n) time := by
    simpa only [Nat.add_zero] using (ResourceOrder.identity dominates).affine positive 2 0
  have sourceOrder := order.affine positive 3 3
  have total : ResourceOrder (fun n => 2 * n + 3 * runtime n + 3) time := by
    simpa only [Nat.add_assoc] using scan.add sourceOrder
  refine ⟨Simulation.TransducerBank.IndexedOutputRecognizer.machine M,
    (fun n => 2 * n + 3 * runtime n + 3), total, ?_, ?_⟩
  · intro word
    exact Simulation.TransducerBank.IndexedOutputRecognizer.timeBound M word (runtime word.length)
      (bounded word.length)
  · intro word
    have terminates : M.Terminates (generatorData word.length) := by
      intro bits
      obtain ⟨ticks, result, _, execution⟩ := bounded word.length bits
      exact ⟨ticks, result, execution⟩
    exact (exists_congr fun bits =>
      Simulation.TransducerBank.IndexedOutputRecognizer.accepts_word_iff M word bits terminates).trans
        (coverage word)

/-- The nonempty finite-seed convention gives the same layer criterion, even
when a machine already accepts on the empty choice tape. -/
theorem indexed_recognizer_accepts_layer (G : UniformGenerators α) (word : Word α) :
    (∃ bits, (Simulation.TransducerBank.IndexedOutputRecognizer.machine G.machine).Accepts
      (decisionData word) bits) ↔ word ∈ G.layer word.length := by
  exact (exists_congr fun bits =>
    Simulation.TransducerBank.IndexedOutputRecognizer.accepts_word_iff G.machine word bits
      (G.isGenerator word.length).1.1).trans
      (G.machine.generatedLanguage_iff_produces (generatorData word.length) word).symm

end
end ComplexityOfGenerators.Multitape
