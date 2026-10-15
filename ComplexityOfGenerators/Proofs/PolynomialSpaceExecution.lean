import ComplexityOfGenerators.Proofs.PolynomialSpaceFrames
import ComplexityOfGenerators.Simulation.SavitchMachine

/-!
# Execution of the recursive generator-membership search

This connects the concrete recursive program to the previously verified
configuration-graph algorithm. The base-test premise describes a uniform
finite graph-test program. `PolynomialSpaceInitialization` and
`PolynomialSpaceDecision` construct the root from physical input and compile
the combined program; `PolynomialSpaceBase` supplies the proved graph tests
and concludes the native containment.
-/

namespace ComplexityOfGenerators

open Simulation Simulation.StackSpace Simulation.SavitchMachine

noncomputable section

variable {α : Type} [Fintype α]

/-- Given the actual base-test implementation, the recursive program halts
with exactly the generator-membership answer. Its entire execution, including
scratch storage and the persistent input, obeys the polynomial stack bound. -/
theorem generator_membership_trace_of_base (M : Machine Unit Bool α) (space : PolynomialBound)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n)) (word : List α)
    {B : Type} (baseEntry : B) (base : B → WithInput.Code B) (input : List Frames.Symbol)
    (inputBound : input.length ≤ generatorStackSpace M space word.length)
    (baseCorrect : WithInput.BaseCorrect baseEntry base input
      ((outputMatcher M).spaceReachBase ⟨word, [], word.length⟩ (space word.length))
      ((outputMatcher M).spaceAcceptBase ⟨word, [], word.length⟩ (space word.length))
      (generatorStackSpace M space word.length)) :
    ∃ final : Source Frames.Symbol (Label B) Local 12,
      Trace (WithInput.program baseEntry base) (generatorStackSpace M space word.length)
        (WithInput.encoded input .dispatch (generatorStackRun M space word 0)) final ∧
      final.l = none ∧
      (final.var.1.answer = true ↔ word ∈ M.generatedLanguage (generatorData word.length)) := by
  let matcher := outputMatcher M
  let data : InputData α Bool := ⟨word, [], word.length⟩
  let br := matcher.spaceReachBase data (space word.length)
  let ba := matcher.spaceAcceptBase data (space word.length)
  let codec := matcher.spaceCodeCodec data (space word.length)
  let z := SavitchStack.zeroCode codec
  let initial := generatorStackRun M space word 0
  have run (k : ℕ) : (Complexity.Sav.step br ba z)^[k] initial = generatorStackRun M space word k := rfl
  obtain ⟨steps, before, done, answer⟩ := generatorStackRun_correct M space bounded word
  have path := WithInput.iterate baseEntry base input br ba z initial steps
    (generatorStackSpace M space word.length) inputBound baseCorrect (by
      intro k _ f member
      rw [run] at member
      have width := generatorStackRun_midpointWidth M space word k f member
      change List.replicate codec.width false = List.replicate f.m.length false
      rw [width])
    (by intro k hk; rw [run]; exact before k hk)
    (by intro k _ j; rw [run]; exact generatorStackRun_column_length M space word k j)
  rw [run] at path
  have last := WithInput.halt baseEntry base input (generatorStackRun M space word steps) done
    (generatorStackSpace M space word.length) inputBound (generatorStackRun_column_length M space word steps)
  exact ⟨_, path.trans last, rfl, answer⟩

end
end ComplexityOfGenerators
