import ComplexityOfGenerators.Examples.SATNative.EvaluationModel

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open NativeLiteral NativeAssignment

set_option backward.isDefEq.respectTransparency false

theorem initial_reconstructs (capacity active : ℕ) (bits : List Bool) (word : List Symbol) :
    Reconstructs capacity active bits word (initial word) := by
  intro _
  exact ⟨[], [], by simp [Formula.valid], by simp [Formula.eval], by simp,
    by simp [initial], by simp [initial, Clause.eval], by simp [initial, Formula.bodyWord]⟩

theorem formula_append (done : Formula) (clause : Clause) (bits : List Bool)
    (previous : done.eval (assignment bits) = true) (current : clause.eval (assignment bits) = true) :
    (done ++ [clause]).eval (assignment bits) = true := by
  simpa [Formula.eval, List.all_append] using And.intro previous current

theorem clause_append (clause : Clause) (literal : Literal) (bits : List Bool) :
    (clause ++ [literal]).eval (assignment bits) =
      (clause.eval (assignment bits) || literal.eval (assignment bits)) := by
  simp [Clause.eval, List.any_append]

theorem step_reconstructs {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (original : List Symbol) (state : State)
    (invariant : Reconstructs capacity active bits original state) :
    Reconstructs capacity active bits original (step capacity active (bits.map bitSymbol) state) := by
  intro accepted
  have valid : state.parserState.valid = true := by
    cases good : state.parserState.valid with
    | true => rfl
    | false => have := step_invalid capacity active (bits.map bitSymbol) state good; simp [this] at accepted
  obtain ⟨done, current, good, satisfied, literals, nonempty, truth, reconstruct⟩ := invariant valid
  cases word : state.parserState.word with
  | nil =>
    have fixed : step capacity active (bits.map bitSymbol) state = state := by simp [step, word]
    rw [fixed] at accepted ⊢
    exact invariant accepted
  | cons head rest =>
    by_cases inside : state.parserState.inside = true
    · have body : original = done.bodyWord capacity ++ .openClause ::
          (current.flatMap (Literal.encode capacity) ++ state.parserState.word) := by simpa [inside] using reconstruct
      by_cases close : head = .closeClause
      · have tests : state.parserState.nonempty = true ∧ state.clauseValue = true := by
          simpa [step, word, inside, close, valid] using accepted
        have clauseGood : current.eval (assignment bits) = true := by rw [← truth]; exact tests.2
        refine ⟨done ++ [current], [], NativeBody.valid_append_clause active done current good (nonempty.mp tests.1) literals,
          formula_append done current bits satisfied clauseGood, by simp, ?_, ?_, ?_⟩
        · simp [step, word, inside, close]
        · simp [step, word, inside, close, Clause.eval]
        · simpa [step, word, inside, close, NativeBody.bodyWord_append, Formula.bodyWord, Clause.encode,
            List.append_assoc] using body
      · have parsed : (readLiteral capacity active state.parserState.word).isSome = true := by
          simpa [step, word, inside, close, valid] using accepted
        obtain ⟨literal, decoded⟩ := Option.isSome_iff_exists.mp parsed
        obtain ⟨literalGood, encoding⟩ := readLiteral_sound capacity active state.parserState.word literal decoded
        have literalTruthEq : literalTruth active (bits.map bitSymbol) state.parserState.word capacity =
            literal.eval (assignment bits) := by
          have canonical := literalTruth_encode bound bits length literal literalGood
            (fieldState capacity state.parserState.word).word
          rw [← encoding] at canonical
          exact canonical
        refine ⟨done, current ++ [literal], good, satisfied, ?_, ?_, ?_, ?_⟩
        · intro item member
          rcases List.mem_append.mp member with old | fresh
          · exact literals item old
          · have same : item = literal := by simpa using fresh
            simpa [same] using literalGood
        · simp [step, word, inside, close]
        · have truthHead := literalTruthEq
          rw [word] at truthHead
          simp [step, word, inside, close, clause_append, ← truth, truthHead]
        · rw [encoding] at body
          simpa [step, word, inside, close, List.flatMap_append, List.append_assoc] using body
    · have outside : state.parserState.inside = false := Bool.eq_false_iff.mpr inside
      have previous : current = [] ∧ original = done.bodyWord capacity ++ state.parserState.word := by
        simpa [outside] using reconstruct
      have opening : head = .openClause := by
        by_contra bad
        simp [step, word, outside, bad] at accepted
      refine ⟨done, [], good, satisfied, by simp, ?_, ?_, ?_⟩
      · simp [step, word, outside, opening]
      · simp [step, word, outside, opening, Clause.eval]
      · simpa [step, word, outside, opening] using previous.2

theorem iterate_reconstructs {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (count : ℕ) (word : List Symbol) :
    Reconstructs capacity active bits word
      ((step capacity active (bits.map bitSymbol))^[count] (initial word)) := by
  induction count with
  | zero => exact initial_reconstructs capacity active bits word
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    exact step_reconstructs bound bits length word _ ih

theorem accepted_sound {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (count : ℕ) (word : List Symbol)
    (accepted : accepts ((step capacity active (bits.map bitSymbol))^[count] (initial word)) = true) :
    ∃ formula : Formula, formula.valid active ∧ formula.eval (assignment bits) = true ∧
      word = formula.bodyWord capacity := by
  let final := (step capacity active (bits.map bitSymbol))^[count] (initial word)
  have tests : final.parserState.word = [] ∧ final.parserState.inside = false ∧ final.parserState.valid = true := by
    have parsed : (final.parserState.word = [] ∧ final.parserState.inside = false) ∧ final.parserState.valid = true := by
      simpa [accepts, NativeBody.accepts, final, Bool.and_eq_true, Bool.not_eq_true] using accepted
    exact ⟨parsed.1.1, parsed.1.2, parsed.2⟩
  obtain ⟨done, current, good, satisfied, _, _, _, reconstruct⟩ := iterate_reconstructs bound bits length count word tests.2.2
  refine ⟨done, good, satisfied, ?_⟩
  change (if final.parserState.inside then word = done.bodyWord capacity ++ .openClause ::
    (current.flatMap (Literal.encode capacity) ++ final.parserState.word)
    else current = [] ∧ word = done.bodyWord capacity ++ final.parserState.word) at reconstruct
  simp only [tests.2.1, Bool.false_eq_true, ite_false, tests.1, List.append_nil] at reconstruct
  exact reconstruct.2

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
