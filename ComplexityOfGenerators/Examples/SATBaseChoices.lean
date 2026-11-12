import ComplexityOfGenerators.Examples.SATInverseWords

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

def constantClause (bits : List Bool) : Clause := bits.map Literal.constant

def baseFormula (rows : List (List Bool)) : Formula :=
  rows.map (fun bits => constantClause (forceTrue bits))

def Literal.constantValue : Literal → Bool
  | .constant value => value
  | .var _ _ => false

def Clause.constantBits (c : Clause) : List Bool := c.map Literal.constantValue

theorem Literal.constant_roundtrip (lit : Literal) (valid : lit.valid 0) :
    Literal.constant lit.constantValue = lit := by
  cases lit with
  | constant value => rfl
  | var j sign => have := valid.1; have := valid.2; omega

theorem Clause.constant_roundtrip (c : Clause) (valid : ∀ lit ∈ c, lit.valid 0) :
    constantClause c.constantBits = c := by
  unfold constantClause constantBits
  rw [List.map_map]
  calc
    _ = c.map id := by
      apply List.map_congr_left
      intro lit member
      exact lit.constant_roundtrip (valid lit member)
    _ = c := List.map_id c

@[simp] theorem constantClause_eval (bits : List Bool) (assignment : Assignment) :
    (constantClause bits).eval assignment = bits.any id := by
  simp only [constantClause, Clause.eval, List.any_map, Literal.eval, Function.comp_def]
  rfl

theorem forceTrue_nonempty (bits : List Bool) : forceTrue bits ≠ [] := by
  intro empty
  have truth := forceTrue_true bits
  rw [empty] at truth
  simp at truth

theorem baseFormula_valid (rows : List (List Bool)) : (baseFormula rows).valid 0 := by
  intro c member
  obtain ⟨bits, _, rfl⟩ := List.mem_map.mp member
  constructor
  · intro empty
    have same := congrArg List.length empty
    have := forceTrue_nonempty bits
    simp [constantClause] at same
    exact this same
  · intro lit member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    trivial

theorem baseFormula_satisfiable (rows : List (List Bool)) : Satisfiable 0 (baseFormula rows) := by
  rw [satisfiable_zero_iff]
  simp only [baseFormula, Formula.eval, List.all_eq_true]
  intro c member
  obtain ⟨bits, _, rfl⟩ := List.mem_map.mp member
  rw [constantClause_eval]
  exact forceTrue_true bits

theorem baseFormula_complete (f : Formula) (valid : f.valid 0) (satisfiable : Satisfiable 0 f) :
    baseFormula (f.map Clause.constantBits) = f := by
  have truth := (satisfiable_zero_iff f).mp satisfiable
  unfold Formula.eval at truth
  unfold baseFormula
  rw [List.map_map]
  calc
    _ = f.map id := by
      apply List.map_congr_left
      intro c member
      have recovered := c.constant_roundtrip (valid c member).2
      have each := List.all_eq_true.mp truth c member
      have bitsTrue : c.constantBits.any id = true := by
        rw [← constantClause_eval c.constantBits (fun _ => false), recovered]
        exact each
      rw [Function.comp_apply, forceTrue_fixed _ bitsTrue]
      exact recovered
    _ = f := List.map_id f

/-- The force-one-true-constant construction has exactly the desired base
support. The displayed target-length filter includes all empty targets. -/
theorem bases_choice_image (n : ℕ) :
    selfReduction.bases n = {word | ∃ M rows,
      ((baseFormula rows).encode M 0).length = n ∧ (baseFormula rows).encode M 0 = word} := by
  rw [bases_eq]
  ext word
  constructor
  · rintro ⟨M, f, valid, satisfiable, length, equal⟩
    refine ⟨M, f.map Clause.constantBits, ?_, ?_⟩
    · simpa [baseFormula_complete f valid satisfiable] using length
    · simpa [baseFormula_complete f valid satisfiable] using equal
  · rintro ⟨M, rows, length, equal⟩
    exact ⟨M, baseFormula rows, baseFormula_valid rows, baseFormula_satisfiable rows, length, equal⟩

end ComplexityOfGenerators.Examples.PaddedCNF
