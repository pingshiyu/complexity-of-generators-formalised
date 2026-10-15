import ComplexityOfGenerators.Proofs.PolynomialSpaceStack
import ComplexityOfGenerators.Simulation.SavitchMachine.Alphabet

/-! Initialize the precise root configuration used in the generator-membership
search, starting with the actual source input. This discharges initialization
separately from the configuration-graph base program supplied in `PolynomialSpaceBase`. -/

namespace ComplexityOfGenerators

open Simulation StackSpace SavitchMachine
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

def generatorInitialization (M : Machine Unit Bool α) (space : PolynomialBound) :=
  Initialize.program (Alphabet.write (α := α)) Alphabet.read
    (Complexity.bitsOfLenLE (outputMatcher M).states (outputMatcher M).initial.val)
    (outputMatcher M).symbols space (generatorSearchDepth M space)

def generatorInitializationSpace (M : Machine Unit Bool α) (space : PolynomialBound) : PolynomialBound :=
  Initialize.spaceBound
    (Complexity.bitsOfLenLE (outputMatcher M).states (outputMatcher M).initial.val)
    (outputMatcher M).symbols space (generatorSearchDepth M space)

/-- A uniform finite program constructs the search's actual encoded root.
Its bound includes input loading, both polynomial rulers, the configuration
code and all root-frame scratch space. No correctness premise for another
subprogram occurs in this theorem. -/
theorem generator_initialization_trace (M : Machine Unit Bool α) (space : PolynomialBound) (word : List α) :
    Trace (generatorInitialization M space) (generatorInitializationSpace M space word.length)
      (sourceInitial .load (carrying false false, none) (Alphabet.input word))
      (Alphabet.encoded word (.root .done) (generatorStackRun M space word 0)) := by
  let matcher := outputMatcher M
  let state := Complexity.bitsOfLenLE matcher.states matcher.initial.val
  let depth := generatorSearchDepth M space
  have path := Initialize.run (Alphabet.write (α := α)) Alphabet.read Alphabet.inverse
    state matcher.symbols space depth (Alphabet.input word)
  simp only [Alphabet.input, List.length_map] at path
  have bounded := path.mono (Initialize.radius_le_spaceBound state matcher.symbols space depth word.length)
  have code : InitialVertex.code state matcher.symbols word.length (space word.length) =
      (matcher.spaceCodeCodec ⟨word, [], word.length⟩ (space word.length)).encode
        (matcher.initialSpaceCode ⟨word, [], word.length⟩ (space word.length)) :=
    (matcher.initialSpaceCode_bits_matching word (space word.length)).symm
  rw [code, Root.frame_eq_root] at bounded
  exact bounded

end
end ComplexityOfGenerators
