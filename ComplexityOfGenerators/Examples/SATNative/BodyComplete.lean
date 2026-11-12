import ComplexityOfGenerators.Examples.SATNative.BodyModel

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeBody

open NativeLiteral

set_option backward.isDefEq.respectTransparency false

theorem step_literal {capacity active : ℕ} (bound : active ≤ capacity) (lit : Literal)
    (valid : lit.valid active) (rest : List Symbol) (seen enabled : Bool) :
    step capacity active ⟨lit.encode capacity ++ rest, true, seen, enabled⟩ =
      ⟨rest, true, true, enabled⟩ := by
  have parsed := readLiteral_encode bound lit valid rest
  have recognized : (readLiteral capacity active (lit.encode capacity ++ rest)).isSome = true := by
    rw [parsed.1]
    rfl
  cases lit with
  | constant value =>
    cases value <;> simp [Literal.encode, List.append_assoc] at parsed recognized <;>
      simp [step, Literal.encode, List.append_assoc, parsed.2, recognized]
  | var index sign =>
    cases sign <;> simp [Literal.encode, List.append_assoc] at parsed recognized <;>
      simp [step, Literal.encode, List.append_assoc, parsed.2, recognized]

/-- A clause's literal records use one parser iteration each, although their
native implementation scans every fixed-width record in full. -/
theorem iterate_literals {capacity active : ℕ} (bound : active ≤ capacity) (clause : Clause)
    (valid : ∀ lit ∈ clause, lit.valid active) (rest : List Symbol) (seen enabled : Bool) :
    (step capacity active)^[clause.length]
      ⟨clause.flatMap (Literal.encode capacity) ++ rest, true, seen, enabled⟩ =
        ⟨rest, true, seen || decide (clause ≠ []), enabled⟩ := by
  induction clause generalizing seen with
  | nil => simp
  | cons lit tail ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
      Function.iterate_succ_apply, step_literal bound lit (valid lit (by simp))]
    rw [ih (by intro item member; exact valid item (by simp [member]))]
    simp

theorem iterate_clause {capacity active : ℕ} (bound : active ≤ capacity) (clause : Clause)
    (nonempty : clause ≠ []) (valid : ∀ lit ∈ clause, lit.valid active)
    (rest : List Symbol) (enabled : Bool) :
    (step capacity active)^[clause.length + 2]
      ⟨clause.encode capacity ++ rest, false, false, enabled⟩ =
        ⟨rest, false, false, enabled⟩ := by
  have first : step capacity active ⟨clause.encode capacity ++ rest, false, false, enabled⟩ =
      ⟨clause.flatMap (Literal.encode capacity) ++ .closeClause :: rest, true, false, enabled⟩ := by
    simp [step, Clause.encode, List.append_assoc]
  rw [show clause.length + 2 = clause.length + 1 + 1 by omega, Function.iterate_succ_apply, first,
    Function.iterate_succ_apply']
  rw [iterate_literals bound clause valid]
  simp [step, nonempty]

def tokenCount (formula : Formula) : ℕ := (formula.map (fun clause => clause.length + 2)).sum

theorem tokenCount_cons (clause : Clause) (tail : Formula) :
    tokenCount (clause :: tail) = tokenCount tail + (clause.length + 2) := by simp [tokenCount]; omega

theorem iterate_formula {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (rest : List Symbol) (enabled : Bool) :
    (step capacity active)^[tokenCount formula]
      ⟨formula.bodyWord capacity ++ rest, false, false, enabled⟩ =
        ⟨rest, false, false, enabled⟩ := by
  induction formula with
  | nil => simp [tokenCount, Formula.bodyWord]
  | cons clause tail ih =>
    have headGood := valid clause (by simp)
    rw [tokenCount_cons, Function.iterate_add_apply]
    rw [show Formula.bodyWord capacity (clause :: tail) ++ rest =
      clause.encode capacity ++ (Formula.bodyWord capacity tail ++ rest) by
        simp [Formula.bodyWord, List.append_assoc]]
    change (step capacity active)^[tokenCount tail]
      ((step capacity active)^[clause.length + 2]
        ⟨clause.encode capacity ++ (Formula.bodyWord capacity tail ++ rest), false, false, enabled⟩) = _
    rw [iterate_clause bound clause headGood.1 headGood.2]
    exact ih (by intro c member; exact valid c (by simp [member]))

theorem tokenCount_bound {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) : tokenCount formula ≤ (formula.bodyWord capacity).length := by
  induction formula with
  | nil => simp [tokenCount, Formula.bodyWord]
  | cons clause tail ih =>
    have tailBound := ih (by intro c member; exact valid c (by simp [member]))
    have headLength := Clause.encode_length bound clause (valid clause (by simp)).2
    have headCount : clause.length + 2 ≤ (clause.encode capacity).length := by
      rw [headLength]
      nlinarith
    rw [tokenCount_cons]
    change tokenCount tail + (clause.length + 2) ≤ (clause.encode capacity ++ Formula.bodyWord capacity tail).length
    rw [List.length_append]
    omega

theorem iterate_empty_fixed (capacity active count : ℕ) (inside seen enabled : Bool) :
    (step capacity active)^[count] ⟨[], inside, seen, enabled⟩ = ⟨[], inside, seen, enabled⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [Function.iterate_succ_apply, step] using ih

theorem accepted_encode {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (count : ℕ) (enough : tokenCount formula ≤ count) :
    accepts ((step capacity active)^[count] (initial (formula.bodyWord capacity))) = true := by
  have encoding := iterate_formula bound formula valid [] true
  simp only [List.append_nil] at encoding
  rw [show count = (count - tokenCount formula) + tokenCount formula by omega,
    Function.iterate_add_apply]
  change accepts ((step capacity active)^[count - tokenCount formula]
    ((step capacity active)^[tokenCount formula]
      ⟨formula.bodyWord capacity, false, false, true⟩)) = true
  rw [encoding, iterate_empty_fixed]
  rfl

theorem accepted_iff {capacity active : ℕ} (bound : active ≤ capacity) (word : List Symbol) :
    accepts ((step capacity active)^[word.length] (initial word)) = true ↔
      ∃ formula : Formula, formula.valid active ∧ word = formula.bodyWord capacity := by
  constructor
  · exact accepted_sound capacity active word.length word
  · rintro ⟨formula, valid, rfl⟩
    exact accepted_encode bound formula valid _ (tokenCount_bound bound formula valid)

end ComplexityOfGenerators.Examples.PaddedCNF.NativeBody
