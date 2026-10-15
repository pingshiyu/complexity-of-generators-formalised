import ComplexityOfGenerators.Proofs.PolynomialSpaceSearch
import ComplexityOfGenerators.Foundations.SpaceCodeBits
import ComplexityOfGenerators.Simulation.SavitchMachine.Counter

/-!
# The Savitch stack for Theorem 6.1

Following Appendix A.17, the streaming comparator reduces generation to a
configuration graph, and the verified Complexitylib stack performs midpoint
search. It halts with the correct answer and its serialized state has a uniform
polynomial size bound at every step.

`StackSpace.mem_pspace` now compiles finite Mathlib stack programs with bounded
reachable stacks into the retained native machine, including temporary work.
The recursive finite control, frame operations and counter are implemented in
`SavitchMachine`; `PolynomialSpaceDecision` connects their bounded traces to
this algorithm. `PolynomialSpaceInitialization` constructs the root from the
input; `PolynomialSpaceDecision` supplies native compilation and composition.
The configuration-graph base program and containment are completed in
`PolynomialSpaceBase`.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section

variable {α : Type} [Fintype α]

def generatorStackRun (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (steps : ℕ) : Complexity.Sav.Sst :=
  (outputMatcher M).spaceStackRun ⟨word, [], word.length⟩ (space word.length)
    (generatorSearchDepth M space word.length) steps

/-- A uniform polynomial bound for the encoded stack, including size zero. -/
def generatorStackSpace (M : Machine Unit Bool α) (space : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (44 * ((generatorSearchDepth M space).asPolynomial + 1) ^ 2)

theorem generatorStackRun_encoded_length (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (steps : ℕ) :
    (Complexity.encSst [] (generatorStackRun M space word steps)).length ≤
      generatorStackSpace M space word.length := by
  have stackBound := (outputMatcher M).spaceStackRun_encoded_length
    ⟨word, [], word.length⟩ (space word.length) (generatorSearchDepth M space word.length) steps
  have square := SavitchStack.encodedSizeBound_le_square (generatorSearchDepth_bound M space word)
  have polynomial := PolynomialBound.eval_le_ofPolynomial
    (44 * ((generatorSearchDepth M space).asPolynomial + 1) ^ 2) word.length
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, PolynomialBound.asPolynomial_eval, Polynomial.eval_one] at polynomial
  exact stackBound.trans (square.trans polynomial)

/-- The actual library stack evaluator halts with the membership answer.
This theorem makes no halting assumption about the source generator. -/
theorem generatorStackRun_correct (M : Machine Unit Bool α) (space : PolynomialBound)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n)) (word : List α) :
    ∃ steps,
      (∀ j < steps, (generatorStackRun M space word j).done = false) ∧
      (generatorStackRun M space word steps).done = true ∧
      ((generatorStackRun M space word steps).ans = true ↔
        word ∈ M.generatedLanguage (generatorData word.length)) := by
  have matcherSpace := outputMatcher_spaceBound M ⟨word, [], word.length⟩ (space word.length)
    (bounded word.length)
  obtain ⟨steps, _, before, done, answer⟩ := matcherSpace.spaceStackRun_correct (outputMatcher M)
    (generatorSearchDepth M space word.length) (generatorSearchDepth_bound M space word)
  refine ⟨steps, before, done, answer.trans ?_⟩
  exact (matcherSpace.spaceSearch_correct (outputMatcher M) _
    (generatorSearchDepth_bound M space word)).symm.trans
      (generatorSpaceSearch_correct M space bounded word)

/-- Every language in `PSPACEG` has the uniform, terminating library-stack
algorithm with a polynomial bound on its serialized states. Native machine
space complexity is deliberately not inferred from this representation bound. -/
theorem pspaceg_has_polynomialSize_stack {L : Language α} (member : L ∈ PSPACEG α) :
    ∃ (G : GeneratorFamily α) (space stackSpace : PolynomialBound),
      G.toUniformGenerators.language = L ∧
      G.toUniformGenerators.RunsInSpace space ∧
      (∀ word steps,
        (Complexity.encSst [] (generatorStackRun G.machine space word steps)).length ≤
          stackSpace word.length) ∧
      ∀ word, ∃ steps,
        (∀ j < steps, (generatorStackRun G.machine space word j).done = false) ∧
        (generatorStackRun G.machine space word steps).done = true ∧
        ((generatorStackRun G.machine space word steps).ans = true ↔ word ∈ L) := by
  obtain ⟨G, language, space, bounded⟩ := member
  refine ⟨G, space, generatorStackSpace G.machine space, language, bounded,
    generatorStackRun_encoded_length G.machine space, ?_⟩
  intro word
  obtain ⟨steps, before, done, answer⟩ := generatorStackRun_correct G.machine space bounded word
  refine ⟨steps, before, done, answer.trans ?_⟩
  change word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ L
  rw [G.layer_eq_lengthSlice, language]
  exact ⟨fun member => member.1, fun member => ⟨member, rfl⟩⟩

end
end ComplexityOfGenerators
