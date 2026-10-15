import ComplexityOfGenerators.Proofs.PolynomialSpaceBaseBounds
import ComplexityOfGenerators.Proofs.PolynomialSpaceDecision
import ComplexityOfGenerators.Simulation.SavitchMachine.EdgeQueries
import ComplexityOfGenerators.Simulation.SavitchMachine.GraphBase

/-! Complete the native Savitch decider for a polynomial-space generator.
The bounded configuration predicates are implemented by finite stack programs,
then attached to the already verified initializer and recursive interpreter.
No graph-testing oracle or additional complexity assumption is used. -/

namespace ComplexityOfGenerators

open Simulation SavitchMachine StackSpace
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {α : Type} [Fintype α]

abbrev GeneratorBaseContext (G : Machine Unit Bool α) (space : PolynomialBound) :=
  GraphBase.Context (fun word : List α => generatorStackSpace G space word.length)

/-- Select the top frame's two endpoints without changing any parent column. -/
def generatorBaseEndpoints (G : Machine Unit Bool α) (space : PolynomialBound)
    (x : GeneratorBaseContext G space) : PairQueries.Context (outputMatcher G) space where
  source :=
    { word := x.word
      bits := x.frame.u
      parents := (Frames.column x.parents 3).map Alphabet.write
      radius := generatorStackSpace G space x.word.length
      columnRoom := by
        have h := x.bound 3
        simp [Frames.column_cons, Frames.field] at h ⊢
        omega
      rulerRoom := (generator_base_storage_room G space x.word).1
      decoderRoom := generator_header_decoder_room G space x.word
      offsetRoom := generator_header_offset_room G space x.word }
  target := x.frame.v
  parents := (Frames.column x.parents 4).map Alphabet.write
  targetRoom := by
    have h := x.bound 4
    simp [Frames.column_cons, Frames.field] at h ⊢
    omega

def generatorBaseSlots : Fin 9 ↪ Fin 13 := ⟨![6, 7, 8, 9, 10, 11, 12, 3, 4], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

theorem generatorBase_layout (G : Machine Unit Bool α) (space : PolynomialBound)
    (x : GeneratorBaseContext G space) (j : Fin 9) :
    GraphBase.memory x (generatorBaseSlots j) = PairQueries.memory (generatorBaseEndpoints G space x) j := by
  fin_cases j <;> simp [GraphBase.memory, GraphBase.frameMemory, generatorBaseSlots,
    PairQueries.memory, PairQuery.memory, generatorBaseEndpoints, PairQueries.Context.column,
    Frames.column_cons, Frames.field]

/-- The complete configuration-graph base program exists uniformly in the
input word. Its code depends only on the generator and its polynomial bound. -/
theorem generator_configuration_base (G : Machine Unit Bool α) (space : PolynomialBound) :
    ∃ (B : Type) (_ : Fintype B) (entry : B) (base : B → AlphabetSearch.Code α B),
      ∀ word, AlphabetSearch.BaseCorrect entry base word
        ((outputMatcher G).spaceReachBase ⟨word, [], word.length⟩ (space word.length))
        ((outputMatcher G).spaceAcceptBase ⟨word, [], word.length⟩ (space word.length))
        (generatorStackSpace G space word.length) := by
  classical
  apply GraphBase.exists_base (fun word => generatorStackSpace G space word.length)
    (generatorStackSpace_input G space)
    (fun word => (outputMatcher G).spaceReachBase ⟨word, [], word.length⟩ (space word.length))
    (fun word => (outputMatcher G).spaceAcceptBase ⟨word, [], word.length⟩ (space word.length))
  · have localTest := PairQueries.lift_source (ObservationQueries.accept_realizable (outputMatcher G) space)
    have framed := localTest.comap (generatorBaseEndpoints G space)
    exact framed.embed generatorBaseSlots GraphBase.memory (generatorBase_layout G space)
      (GraphBase.memory_bound (generatorStackSpace_input G space))
  · have framed := (EdgeQueries.reach_realizable (outputMatcher G) space).comap (generatorBaseEndpoints G space)
    exact framed.embed generatorBaseSlots GraphBase.memory (generatorBase_layout G space)
      (GraphBase.memory_bound (generatorStackSpace_input G space))

/-- The forward direction of Theorem 6.1. Streaming output comparison reduces
membership to bounded configuration reachability. Savitch midpoint recursion,
including its finite leaf programs, compiles to a native polynomial-space
machine; random tape length and running time need no polynomial bound. -/
theorem pspaceg_subset_pspace : PSPACEG α ⊆ PSPACE α := by
  intro L member
  obtain ⟨G, language, space, bounded⟩ := member
  obtain ⟨B, finite, entry, base, correct⟩ := generator_configuration_base G.machine space
  letI : Fintype B := finite
  have decider := generator_language_mem_pspace_of_base G.machine space bounded entry base correct
  have same : {word | word ∈ G.machine.generatedLanguage (generatorData word.length)} = L := by
    ext word
    change word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ L
    rw [G.layer_eq_lengthSlice, language]
    exact ⟨fun member => member.1, fun member => ⟨member, rfl⟩⟩
  rwa [same] at decider

end
end ComplexityOfGenerators
