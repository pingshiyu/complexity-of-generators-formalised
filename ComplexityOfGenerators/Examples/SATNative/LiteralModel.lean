import ComplexityOfGenerators.Examples.SATNative.HeaderBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral

open NativeHeader

def ofTag (active : ℕ) (tag : Symbol) (index : ℕ) : Option Literal :=
  match tag with
  | .trueConstant => if index = 0 then some (.constant true) else none
  | .falseConstant => if index = 0 then some (.constant false) else none
  | .positive => if 0 < index ∧ index ≤ active then some (.var index true) else none
  | .negative => if 0 < index ∧ index ≤ active then some (.var index false) else none
  | _ => none

def fieldState (capacity : ℕ) (word : List Symbol) : ScanState :=
  step^[capacity] ⟨word.tail, 0, true, true⟩

def readLiteral (capacity active : ℕ) (word : List Symbol) : Option Literal :=
  let field := fieldState capacity word
  if field.valid then word.head?.bind (fun tag => ofTag active tag field.count) else none

theorem field_canonical (capacity index : ℕ) (bound : index ≤ capacity) (tag : Symbol) (rest : List Symbol) :
    fieldState capacity (tag :: (List.replicate index .one ++ (List.replicate (capacity - index) .zero ++ rest))) =
      ⟨rest, index, decide (capacity - index = 0), true⟩ := by
  have scan := iterate_canonical index (capacity - index) rest
  have total : capacity - index + index = capacity := by omega
  rw [total] at scan
  simpa only [fieldState, List.tail_cons, List.append_assoc] using scan

theorem ofTag_sound (capacity active : ℕ) (tag : Symbol) (index : ℕ) (bound : index ≤ capacity)
    (lit : Literal) (decoded : ofTag active tag index = some lit) :
    lit.valid active ∧ lit.encode capacity = tag :: (List.replicate index .one ++ List.replicate (capacity - index) .zero) := by
  cases tag with
  | trueConstant =>
    simp only [ofTag] at decoded
    split_ifs at decoded with zero
    have equal := Option.some.inj decoded
    subst lit
    subst index
    exact ⟨trivial, by simp [Literal.encode]⟩
  | falseConstant =>
    simp only [ofTag] at decoded
    split_ifs at decoded with zero
    have equal := Option.some.inj decoded
    subst lit
    subst index
    exact ⟨trivial, by simp [Literal.encode]⟩
  | positive =>
    simp only [ofTag] at decoded
    split_ifs at decoded with good
    have equal := Option.some.inj decoded
    subst lit
    exact ⟨good, by simp [Literal.encode]⟩
  | negative =>
    simp only [ofTag] at decoded
    split_ifs at decoded with good
    have equal := Option.some.inj decoded
    subst lit
    exact ⟨good, by simp [Literal.encode]⟩
  | zero | one | separator | openClause | closeClause => simp [ofTag] at decoded

theorem readLiteral_sound (capacity active : ℕ) (word : List Symbol) (lit : Literal)
    (decoded : readLiteral capacity active word = some lit) :
    lit.valid active ∧ word = lit.encode capacity ++ (fieldState capacity word).word := by
  cases word with
  | nil => simp [readLiteral] at decoded
  | cons tag rest =>
    unfold readLiteral at decoded
    dsimp only at decoded
    split_ifs at decoded with valid
    change ofTag active tag (fieldState capacity (tag :: rest)).count = some lit at decoded
    have accepted : (step^[capacity] ⟨rest, 0, true, true⟩).valid = true := valid
    obtain ⟨index, bound, _, payload, number⟩ := iterate_sound capacity rest 0 true accepted
    have indexEq : (fieldState capacity (tag :: rest)).count = index := by simpa [fieldState] using number
    rw [indexEq] at decoded
    obtain ⟨good, encoding⟩ := ofTag_sound capacity active tag index bound lit decoded
    refine ⟨good, ?_⟩
    rw [encoding]
    change tag :: rest = (tag :: (List.replicate index .one ++ List.replicate (capacity - index) .zero)) ++
      (step^[capacity] ⟨rest, 0, true, true⟩).word
    simpa only [List.cons_append, List.append_assoc] using congrArg (tag :: ·) payload

theorem readLiteral_encode {capacity active : ℕ} (bound : active ≤ capacity) (lit : Literal)
    (valid : lit.valid active) (rest : List Symbol) :
    readLiteral capacity active (lit.encode capacity ++ rest) = some lit ∧
      (fieldState capacity (lit.encode capacity ++ rest)).word = rest := by
  cases lit with
  | constant value =>
    cases value with
    | false =>
      have parsed := field_canonical capacity 0 (Nat.zero_le _) .falseConstant rest
      simp only [List.replicate_zero, List.nil_append, Nat.sub_zero] at parsed
      simp [Literal.encode, readLiteral, ofTag, parsed]
    | true =>
      have parsed := field_canonical capacity 0 (Nat.zero_le _) .trueConstant rest
      simp only [List.replicate_zero, List.nil_append, Nat.sub_zero] at parsed
      simp [Literal.encode, readLiteral, ofTag, parsed]
  | var index sign =>
    have fits : index ≤ capacity := valid.2.trans bound
    cases sign with
    | false =>
      have parsed := field_canonical capacity index fits .negative rest
      simp [Literal.encode, readLiteral, ofTag, List.append_assoc, parsed, valid.1, valid.2]
    | true =>
      have parsed := field_canonical capacity index fits .positive rest
      simp [Literal.encode, readLiteral, ofTag, List.append_assoc, parsed, valid.1, valid.2]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral
