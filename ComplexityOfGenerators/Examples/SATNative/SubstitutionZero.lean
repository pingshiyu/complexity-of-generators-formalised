import ComplexityOfGenerators.Examples.SATWordReduction

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

theorem literal_substitute_zero (bit : Bool) (literal : Literal) (valid : literal.valid 0) :
    literal.substitute 0 bit = literal := by
  cases literal with
  | constant value => rfl
  | var index sign => have positive := valid.1; have upper := valid.2; omega

theorem clause_substitute_zero (bit : Bool) (clause : Clause) (valid : ∀ literal ∈ clause, literal.valid 0) :
    clause.map (Literal.substitute 0 bit) = clause := by
  induction clause with
  | nil => rfl
  | cons literal tail ih =>
    rw [List.map_cons, literal_substitute_zero bit literal (valid literal (by simp)), ih]
    intro item member
    exact valid item (by simp [member])

theorem formula_substitute_zero (bit : Bool) (formula : Formula) (valid : formula.valid 0) :
    formula.substitute 0 bit = formula := by
  induction formula with
  | nil => rfl
  | cons clause tail ih =>
    simp only [Formula.substitute, List.map_cons]
    rw [clause_substitute_zero bit clause (valid clause (by simp)).2]
    change clause :: Formula.substitute 0 bit tail = clause :: tail
    rw [ih (by intro c member; exact valid c (by simp [member]))]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
