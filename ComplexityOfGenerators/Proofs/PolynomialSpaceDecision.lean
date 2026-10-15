import ComplexityOfGenerators.Proofs.PolynomialSpaceInitialization
import ComplexityOfGenerators.Proofs.PolynomialSpaceFrames
import ComplexityOfGenerators.Simulation.SavitchMachine.AlphabetSearch
import ComplexityOfGenerators.Simulation.StackSpace.Input

/-! Compile initialization and Savitch recursion into one native decider.
The supplied hypothesis describes the uniform configuration-graph base
program, implemented in `PolynomialSpaceBase`. No initialization, alphabet conversion, termination, or native space
simulation is assumed in this interface. -/

namespace ComplexityOfGenerators

open Simulation StackSpace SavitchMachine
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

theorem generatorStackSpace_input (M : Machine Unit Bool α) (space : PolynomialBound) (word : List α) :
    word.length ≤ generatorStackSpace M space word.length := by
  have depth := generatorSearchDepth_bound M space word
  simp only [Machine.spaceConfigurationExponent, List.length_nil] at depth
  have bound := PolynomialBound.eval_le_ofPolynomial
    (44 * ((generatorSearchDepth M space).asPolynomial + 1) ^ 2) word.length
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, PolynomialBound.asPolynomial_eval, Polynomial.eval_one] at bound
  change word.length ≤ PolynomialBound.ofPolynomial _ word.length
  nlinarith

/-- The recursive search with original language letters on its input stack. -/
theorem generator_alphabet_search_trace (M : Machine Unit Bool α) (space : PolynomialBound)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n)) (word : List α)
    {B : Type} (baseEntry : B) (base : B → AlphabetSearch.Code α B)
    (baseCorrect : AlphabetSearch.BaseCorrect baseEntry base word
      ((outputMatcher M).spaceReachBase ⟨word, [], word.length⟩ (space word.length))
      ((outputMatcher M).spaceAcceptBase ⟨word, [], word.length⟩ (space word.length))
      (generatorStackSpace M space word.length)) :
    ∃ final : Source (Alphabet α) (Label B) (Status × Option (Alphabet α)) 12,
      Trace (AlphabetSearch.program baseEntry base) (generatorStackSpace M space word.length)
        (Alphabet.encoded word .dispatch (generatorStackRun M space word 0)) final ∧
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
  have path := AlphabetSearch.iterate baseEntry base word br ba z initial steps
    (generatorStackSpace M space word.length) (generatorStackSpace_input M space word) baseCorrect (by
      intro k _ f member
      rw [run] at member
      have width := generatorStackRun_midpointWidth M space word k f member
      change List.replicate codec.width false = List.replicate f.m.length false
      rw [width])
    (by intro k hk; rw [run]; exact before k hk)
    (by intro k _ j; rw [run]; exact generatorStackRun_column_length M space word k j)
  rw [run] at path
  have last := AlphabetSearch.halt baseEntry base word (generatorStackRun M space word steps) done
    (generatorStackSpace M space word.length) (generatorStackSpace_input M space word)
    (generatorStackRun_column_length M space word steps)
  exact ⟨_, path.trans last, rfl, answer⟩

abbrev GeneratorDecisionLabel (M : Machine Unit Bool α) (space : PolynomialBound) (B : Type) :=
  Sum (Initialize.Label space.degree (generatorSearchDepth M space).degree) (Label B)

def generatorDecisionProgram (M : Machine Unit Bool α) (space : PolynomialBound)
    {B : Type} (baseEntry : B) (base : B → AlphabetSearch.Code α B) :
    GeneratorDecisionLabel M space B →
      Stmt (Alphabet α) (GeneratorDecisionLabel M space B) (Status × Option (Alphabet α)) 12
  | .inl (.root .done) => .goto fun _ => .inr .dispatch
  | .inl q => embedCode (Function.Embedding.refl _) Sum.inl (generatorInitialization M space q)
  | .inr q => embedCode (Function.Embedding.refl _) Sum.inr (AlphabetSearch.program baseEntry base q)

def generatorDecisionSpace (M : Machine Unit Bool α) (space : PolynomialBound) : PolynomialBound :=
  (generatorInitializationSpace M space).add (generatorStackSpace M space)

/-- A complete source trace beginning at the compiler's input-loading endpoint.
The only supplied subprogram is the configuration-graph base test. -/
theorem generator_decision_trace (M : Machine Unit Bool α) (space : PolynomialBound)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n)) (word : List α)
    {B : Type} (baseEntry : B) (base : B → AlphabetSearch.Code α B)
    (baseCorrect : AlphabetSearch.BaseCorrect baseEntry base word
      ((outputMatcher M).spaceReachBase ⟨word, [], word.length⟩ (space word.length))
      ((outputMatcher M).spaceAcceptBase ⟨word, [], word.length⟩ (space word.length))
      (generatorStackSpace M space word.length)) :
    ∃ final,
      Trace (generatorDecisionProgram M space baseEntry base) (generatorDecisionSpace M space word.length)
        (sourceInitial (.inl .load) (carrying false false, none) (Alphabet.input word)) final ∧
      final.l = none ∧
      (final.var.1.answer = true ↔ word ∈ M.generatedLanguage (generatorData word.length)) := by
  let P := generatorDecisionProgram M space baseEntry base
  let r := generatorDecisionSpace M space word.length
  have sumBound := PolynomialBound.add_le (generatorInitializationSpace M space) (generatorStackSpace M space) word.length
  have prefixBound : generatorInitializationSpace M space word.length ≤ r := by
    dsimp only [r, generatorDecisionSpace]; omega
  have suffixBound : generatorStackSpace M space word.length ≤ r := by
    dsimp only [r, generatorDecisionSpace]; omega
  have initialized := (generator_initialization_trace M space word).mono prefixBound
  have first := initialized.rename_active
    (by simp [Alphabet.encoded, extendConfig, localConfig]) Sum.inl P (by
      intro q nonhalt
      cases q with
      | root pc => cases pc <;> first | rfl | exact False.elim (nonhalt rfl)
      | _ => rfl)
  obtain ⟨final, search, halted, answer⟩ := generator_alphabet_search_trace M space bounded word baseEntry base baseCorrect
  have last := (search.mono suffixBound).rename Sum.inr P (fun _ => rfl)
  have handoff : Turing.TM2.step P
      (renameConfig Sum.inl (Alphabet.encoded word (.root .done) (generatorStackRun M space word 0))) =
      some (renameConfig Sum.inr (Alphabet.encoded word (.dispatch : Label B) (generatorStackRun M space word 0))) := rfl
  refine ⟨renameConfig Sum.inr final, first.trans (.step first.end_bound handoff last), ?_, answer⟩
  simp [renameConfig, halted]

/-- Native PSPACE follows once a finite base program has been proved correct.
This theorem supplies the rest of the machine construction, including all
visited-cell bounds and termination on every original input word. -/
theorem generator_language_mem_pspace_of_base (M : Machine Unit Bool α) (space : PolynomialBound)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n))
    {B : Type} [Fintype B] (baseEntry : B) (base : B → AlphabetSearch.Code α B)
    (baseCorrect : ∀ word, AlphabetSearch.BaseCorrect baseEntry base word
      ((outputMatcher M).spaceReachBase ⟨word, [], word.length⟩ (space word.length))
      ((outputMatcher M).spaceAcceptBase ⟨word, [], word.length⟩ (space word.length))
      (generatorStackSpace M space word.length)) :
    {word | word ∈ M.generatedLanguage (generatorData word.length)} ∈ PSPACE α := by
  apply mem_pspace_of_encoded_trace (generatorDecisionProgram M space baseEntry base) (.inl .load)
    (carrying false false, none) (fun v => v.1.answer) Sum.inl _ (generatorDecisionSpace M space)
  intro word
  exact generator_decision_trace M space bounded word baseEntry base (baseCorrect word)

end
end ComplexityOfGenerators
