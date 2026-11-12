import ComplexityOfGenerators.Examples.SATInverseWords

/-! Finite masks for the native SAT inverse. Clause rows are read from one
flat coin block; padding and unused suffixes do not change the lifted formula. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

set_option backward.isDefEq.respectTransparency false

def canonicalChoice (count : ℕ) (choices : List Bool) : List Bool :=
  choices.take count ++ List.replicate (count - choices.length) false

@[simp] theorem canonicalChoice_length (count : ℕ) (choices : List Bool) :
    (canonicalChoice count choices).length = count := by
  simp [canonicalChoice]
  omega

theorem lift_canonicalChoice (d : ℕ) (bit : Bool) (clause : Clause) (choices : List Bool) :
    clause.lift d bit (canonicalChoice clause.length choices) = clause.lift d bit choices := by
  induction clause generalizing choices with
  | nil => rfl
  | cons literal rest ih =>
      cases choices with
      | nil => simpa [canonicalChoice, Clause.lift, List.replicate_succ] using
          congrArg (literal.lift d bit false :: ·) (ih [])
      | cons choiceBit choices =>
          simpa [canonicalChoice, Clause.lift] using
            congrArg (literal.lift d bit choiceBit :: ·) (ih choices)

theorem lift_take (d : ℕ) (bit : Bool) (clause : Clause) (choices : List Bool) :
    clause.lift d bit (choices.take clause.length) = clause.lift d bit choices := by
  induction clause generalizing choices with
  | nil => rfl
  | cons literal rest ih =>
      cases choices <;> simp [Clause.lift, ih]

def canonicalRows : Formula → List (List Bool) → List (List Bool)
  | [], _ => []
  | clause :: rest, choices =>
      canonicalChoice clause.length (choices.headD []) :: canonicalRows rest choices.tail

@[simp] theorem canonicalRows_length (formula : Formula) (choices : List (List Bool)) :
    (canonicalRows formula choices).length = formula.length := by
  induction formula generalizing choices <;> simp [canonicalRows, *]

@[simp] theorem canonicalRows_flatten_length (formula : Formula) (choices : List (List Bool)) :
    (canonicalRows formula choices).flatten.length = formula.occurrences := by
  induction formula generalizing choices <;> simp [canonicalRows, Formula.occurrences, *]

theorem lift_canonicalRows (d : ℕ) (bit : Bool) (formula : Formula) (choices : List (List Bool)) :
    formula.lift d bit (canonicalRows formula choices) = formula.lift d bit choices := by
  induction formula generalizing choices with
  | nil => rfl
  | cons clause rest ih => simp [canonicalRows, Formula.lift, lift_canonicalChoice, ih]

def choiceRows : Formula → BitString → List (List Bool)
  | [], _ => []
  | clause :: rest, bits => bits.take clause.length :: choiceRows rest (bits.drop clause.length)

theorem choiceRows_canonical (formula : Formula) (choices : List (List Bool)) (tail : BitString) :
    choiceRows formula ((canonicalRows formula choices).flatten ++ tail) = canonicalRows formula choices := by
  induction formula generalizing choices with
  | nil => rfl
  | cons clause rest ih =>
      simp only [canonicalRows, List.flatten_cons, List.append_assoc, choiceRows]
      have width := canonicalChoice_length clause.length (choices.headD [])
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
      rw [ih]

theorem lift_flat_block_complete (d : ℕ) (bit : Bool) (formula : Formula)
    (choices : List (List Bool)) (budget : ℕ) (enough : formula.occurrences ≤ budget) :
    ∃ bits : BitString, bits.length = budget ∧
      formula.lift d bit (choiceRows formula bits) = formula.lift d bit choices := by
  let canonical := canonicalRows formula choices
  let bits := canonical.flatten ++ List.replicate (budget - formula.occurrences) false
  refine ⟨bits, ?_, ?_⟩
  · simp only [bits, List.length_append, List.length_replicate, canonical, canonicalRows_flatten_length]
    omega
  · rw [show choiceRows formula bits = canonicalRows formula choices from
      choiceRows_canonical formula choices _]
    exact lift_canonicalRows d bit formula choices

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
