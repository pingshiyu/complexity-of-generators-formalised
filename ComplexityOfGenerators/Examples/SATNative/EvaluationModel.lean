import ComplexityOfGenerators.Examples.SATNative.CertificateCheck

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open NativeLiteral NativeAssignment

structure State where
  parserState : NativeBody.State
  clauseValue : Bool
  deriving DecidableEq

def literalTruth (active : ℕ) (certificate word : List Symbol) (capacity : ℕ) : Bool :=
  value word.head? (certificate.drop (active - (fieldState capacity word).count)).head?

def step (capacity active : ℕ) (certificate : List Symbol) (state : State) : State :=
  match state.parserState.word with
  | [] => state
  | head :: rest =>
      if !state.parserState.inside then
        if head = .openClause then ⟨⟨rest, true, false, state.parserState.valid⟩, false⟩
        else ⟨⟨rest, false, false, false⟩, false⟩
      else if head = .closeClause then
        ⟨⟨rest, false, false, state.parserState.valid && state.parserState.nonempty && state.clauseValue⟩, false⟩
      else ⟨⟨(fieldState capacity state.parserState.word).word, true, true,
        state.parserState.valid && (readLiteral capacity active state.parserState.word).isSome⟩,
        state.clauseValue || literalTruth active certificate state.parserState.word capacity⟩

def initial (word : List Symbol) (enabled : Bool := true) : State := ⟨⟨word, false, false, enabled⟩, false⟩
def accepts (state : State) : Bool := NativeBody.accepts state.parserState

theorem literalTruth_encode {capacity active : ℕ} (bound : active ≤ capacity)
    (bits : List Bool) (length : bits.length = active) (literal : Literal) (valid : literal.valid active)
    (rest : List Symbol) :
    literalTruth active (bits.map bitSymbol) (literal.encode capacity ++ rest) capacity =
      literal.eval (assignment bits) := by
  have parsed := readLiteral_encode bound literal valid rest
  cases literal with
  | constant bit => cases bit <;> simp [literalTruth, value, Literal.encode, Literal.eval]
  | var index sign =>
    have count : (fieldState capacity ((Literal.var index sign).encode capacity ++ rest)).count = index := by
      have fits : index ≤ capacity := valid.2.trans bound
      cases sign <;>
        simpa [Literal.encode, List.append_assoc] using
          congrArg NativeHeader.ScanState.count (field_canonical capacity index fits _ rest)
    have selected : ((bits.map bitSymbol).drop (active - index)).head? =
        some (bitSymbol (assignment bits index)) := by
      simp only [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, List.getElem?_map]
      rw [← length, assignment_at bits index valid.1 (by simpa only [length] using valid.2)]
      rfl
    unfold literalTruth
    rw [count, selected]
    cases sign <;> cases result : assignment bits index <;>
      simp [value, Literal.encode, bitSymbol, Literal.eval, result]

theorem step_invalid (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (invalid : state.parserState.valid = false) :
    (step capacity active certificate state).parserState.valid = false := by
  cases word : state.parserState.word with
  | nil => simp [step, word, invalid]
  | cons head rest => simp only [step, word]; split_ifs <;> simp [invalid]

/-- Evaluation reconstructs actual encoded syntax, and every completed
clause is true under this one certificate assignment. -/
def Reconstructs (capacity active : ℕ) (bits : List Bool) (original : List Symbol) (state : State) : Prop :=
  state.parserState.valid = true → ∃ (done : Formula) (current : Clause),
    done.valid active ∧ done.eval (assignment bits) = true ∧
    (∀ literal ∈ current, literal.valid active) ∧
    (state.parserState.nonempty = true ↔ current ≠ []) ∧
    (state.clauseValue = current.eval (assignment bits)) ∧
    (if state.parserState.inside then
      original = done.bodyWord capacity ++ .openClause ::
        (current.flatMap (Literal.encode capacity) ++ state.parserState.word)
    else current = [] ∧ original = done.bodyWord capacity ++ state.parserState.word)

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
