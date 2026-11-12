import ComplexityOfGenerators.Examples.SATNative.EvaluationSound

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open NativeLiteral NativeAssignment

set_option backward.isDefEq.respectTransparency false

theorem step_literal {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (literal : Literal) (valid : literal.valid active)
    (rest : List Symbol) (seen enabled truth : Bool) :
    step capacity active (bits.map bitSymbol) ⟨⟨literal.encode capacity ++ rest, true, seen, enabled⟩, truth⟩ =
      ⟨⟨rest, true, true, enabled⟩, truth || literal.eval (assignment bits)⟩ := by
  have parsed := readLiteral_encode bound literal valid rest
  have recognized : (readLiteral capacity active (literal.encode capacity ++ rest)).isSome = true := by rw [parsed.1]; rfl
  have evaluated := literalTruth_encode bound bits length literal valid rest
  cases literal with
  | constant value =>
    cases value <;> simp [Literal.encode, List.append_assoc] at parsed recognized evaluated <;>
      simp [step, Literal.encode, List.append_assoc, parsed.2, recognized, evaluated]
  | var index sign =>
    cases sign <;> simp [Literal.encode, List.append_assoc] at parsed recognized evaluated <;>
      simp [step, Literal.encode, List.append_assoc, parsed.2, recognized, evaluated]

theorem iterate_literals {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (clause : Clause) (valid : ∀ literal ∈ clause, literal.valid active)
    (rest : List Symbol) (seen enabled truth : Bool) :
    (step capacity active (bits.map bitSymbol))^[clause.length]
      ⟨⟨clause.flatMap (Literal.encode capacity) ++ rest, true, seen, enabled⟩, truth⟩ =
        ⟨⟨rest, true, seen || decide (clause ≠ []), enabled⟩, truth || clause.eval (assignment bits)⟩ := by
  induction clause generalizing seen truth with
  | nil => simp [Clause.eval]
  | cons literal tail ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
      Function.iterate_succ_apply, step_literal bound bits length literal (valid literal (by simp))]
    rw [ih (by intro item member; exact valid item (by simp [member]))]
    simp [Clause.eval, Bool.or_assoc]

theorem iterate_clause {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (clause : Clause) (nonempty : clause ≠ [])
    (valid : ∀ literal ∈ clause, literal.valid active) (rest : List Symbol) (enabled truth : Bool) :
    (step capacity active (bits.map bitSymbol))^[clause.length + 2]
      ⟨⟨clause.encode capacity ++ rest, false, false, enabled⟩, truth⟩ =
        ⟨⟨rest, false, false, enabled && clause.eval (assignment bits)⟩, false⟩ := by
  have first : step capacity active (bits.map bitSymbol)
      ⟨⟨clause.encode capacity ++ rest, false, false, enabled⟩, truth⟩ =
      ⟨⟨clause.flatMap (Literal.encode capacity) ++ .closeClause :: rest, true, false, enabled⟩, false⟩ := by
    simp [step, Clause.encode, List.append_assoc]
  rw [show clause.length + 2 = clause.length + 1 + 1 by omega, Function.iterate_succ_apply, first,
    Function.iterate_succ_apply']
  rw [iterate_literals bound bits length clause valid]
  simp [step, nonempty]

theorem iterate_formula {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (formula : Formula) (valid : formula.valid active)
    (rest : List Symbol) (enabled : Bool) :
    (step capacity active (bits.map bitSymbol))^[NativeBody.tokenCount formula]
      ⟨⟨formula.bodyWord capacity ++ rest, false, false, enabled⟩, false⟩ =
        ⟨⟨rest, false, false, enabled && formula.eval (assignment bits)⟩, false⟩ := by
  induction formula generalizing enabled with
  | nil => simp [NativeBody.tokenCount, Formula.bodyWord, Formula.eval]
  | cons clause tail ih =>
    have headGood := valid clause (by simp)
    rw [NativeBody.tokenCount_cons, Function.iterate_add_apply]
    rw [show Formula.bodyWord capacity (clause :: tail) ++ rest =
      clause.encode capacity ++ (Formula.bodyWord capacity tail ++ rest) by
        simp [Formula.bodyWord, List.append_assoc]]
    rw [iterate_clause bound bits length clause headGood.1 headGood.2]
    rw [ih (by intro c member; exact valid c (by simp [member]))]
    simp [Formula.eval, Bool.and_assoc]

theorem iterate_empty_fixed (capacity active count : ℕ) (certificate : List Symbol)
    (inside seen enabled truth : Bool) :
    (step capacity active certificate)^[count] ⟨⟨[], inside, seen, enabled⟩, truth⟩ =
      ⟨⟨[], inside, seen, enabled⟩, truth⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [Function.iterate_succ_apply, step] using ih

theorem evaluate_encode {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (formula : Formula) (valid : formula.valid active)
    (count : ℕ) (enough : NativeBody.tokenCount formula ≤ count) :
    accepts ((step capacity active (bits.map bitSymbol))^[count] (initial (formula.bodyWord capacity))) =
      formula.eval (assignment bits) := by
  have encoding := iterate_formula bound bits length formula valid [] true
  simp only [List.append_nil] at encoding
  rw [show count = (count - NativeBody.tokenCount formula) + NativeBody.tokenCount formula by omega,
    Function.iterate_add_apply]
  change accepts ((step capacity active (bits.map bitSymbol))^[count - NativeBody.tokenCount formula]
    ((step capacity active (bits.map bitSymbol))^[NativeBody.tokenCount formula]
      ⟨⟨formula.bodyWord capacity, false, false, true⟩, false⟩)) = _
  rw [encoding, iterate_empty_fixed]
  simp [accepts, NativeBody.accepts]

theorem accepted_iff {capacity active : ℕ} (bound : active ≤ capacity) (bits : List Bool)
    (length : bits.length = active) (word : List Symbol) :
    accepts ((step capacity active (bits.map bitSymbol))^[word.length] (initial word)) = true ↔
      ∃ formula : Formula, formula.valid active ∧ formula.eval (assignment bits) = true ∧ word = formula.bodyWord capacity := by
  constructor
  · exact accepted_sound bound bits length word.length word
  · rintro ⟨formula, valid, satisfied, rfl⟩
    rw [evaluate_encode bound bits length formula valid _ (NativeBody.tokenCount_bound bound formula valid)]
    exact satisfied

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
