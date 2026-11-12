import ComplexityOfGenerators.Examples.SATBaseChoices

/-! Productive SAT base lengths and concrete linear-size fallbacks for the
proposal-and-check native base generator. -/
namespace ComplexityOfGenerators.Examples.PaddedCNF
set_option backward.isDefEq.respectTransparency false

/-- Two header separators; the capacity-one empty formula; or a single true
constant clause. The last case works at every length at least five. -/
def baseDefault (n : ℕ) : List Symbol :=
  if n = 2 then Formula.encode 0 0 []
  else if n = 4 then Formula.encode 1 0 []
  else Formula.encode 0 0 [List.replicate (n-4) (Literal.constant true)]

def BaseProductive (n : ℕ) : Prop := 2 ≤ n ∧ n ≠ 3

instance (n : ℕ) : Decidable (BaseProductive n) := by unfold BaseProductive; infer_instance

theorem trueClause_valid (count : ℕ) (positive : 0 < count) :
    Formula.valid 0 [List.replicate count (Literal.constant true)] := by
  intro clause member
  have equal : clause = List.replicate count (Literal.constant true) := by simpa using member
  subst clause
  constructor
  · intro empty
    have := congrArg List.length empty
    simp at this
    omega
  · intro literal member
    have equal : literal = Literal.constant true := List.eq_of_mem_replicate member
    subst literal
    trivial

theorem trueClause_satisfiable (count : ℕ) (positive : 0 < count) :
    Satisfiable 0 [List.replicate count (Literal.constant true)] := by
  rw [satisfiable_zero_iff]
  cases count with
  | zero => omega
  | succ count => simp [Formula.eval, Clause.eval, Literal.eval]

theorem baseDefault_mem (n : ℕ) (productive : BaseProductive n) :
    baseDefault n ∈ selfReduction.bases n := by
  rw [bases_eq]
  by_cases two : n = 2
  · subst n
    refine ⟨0, [], by simp [Formula.valid], ?_, by decide, by simp [baseDefault]⟩
    rw [satisfiable_zero_iff]
    rfl
  · by_cases four : n = 4
    · subst n
      refine ⟨1, [], by simp [Formula.valid], ?_, by decide, by simp [baseDefault]⟩
      rw [satisfiable_zero_iff]
      rfl
    · have large : 5 ≤ n := by rcases productive with ⟨_, _⟩; omega
      have positive : 0 < n-4 := by omega
      refine ⟨0, [List.replicate (n-4) (Literal.constant true)], trueClause_valid _ positive,
        trueClause_satisfiable _ positive, ?_, by simp [baseDefault, two, four]⟩
      rw [Formula.encode_length (by omega) _ (trueClause_valid _ positive)]
      simp [Formula.occurrences]
      omega

theorem bases_productive_iff (n : ℕ) : (selfReduction.bases n).Nonempty ↔ BaseProductive n := by
  constructor
  · rintro ⟨word, member⟩
    rw [bases_eq] at member
    obtain ⟨M, formula, valid, _, length, _⟩ := member
    rw [Formula.encode_length (by omega) _ valid] at length
    refine ⟨by omega, ?_⟩
    intro three
    rw [three] at length
    have zeroCapacity : M = 0 := by omega
    subst M
    have noClauses : formula.length = 0 := by omega
    have empty : formula = [] := List.length_eq_zero_iff.mp noClauses
    simp [empty, Formula.occurrences] at length
  · intro productive
    exact ⟨baseDefault n, baseDefault_mem n productive⟩

theorem baseDefault_length (n : ℕ) (productive : BaseProductive n) :
    (baseDefault n).length = n := by
  have member := baseDefault_mem n productive
  rw [bases_eq] at member
  obtain ⟨_, _, _, _, length, equal⟩ := member
  simpa only [equal] using length

/-- Explicit word templates used by the native fallback emitter. -/
theorem baseDefault_long (n : ℕ) (large : 5 ≤ n) :
    baseDefault n = [.separator, .separator, .openClause] ++
      List.replicate (n-4) .trueConstant ++ [.closeClause] := by
  have two : n ≠ 2 := by omega
  have four : n ≠ 4 := by omega
  simp [baseDefault, two, four, Formula.encode, Clause.encode, Literal.encode,
    List.flatMap_replicate]

end ComplexityOfGenerators.Examples.PaddedCNF
