import ComplexityOfGenerators.Examples.SATNative.LiteralBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeBody

open NativeLiteral

/-- Parser control after a complete token: delimiters cost one step and a
padded literal costs one step. The concrete stack implementation scans its
fixed-width payload internally. -/
structure State where
  word : List Symbol
  inside : Bool
  nonempty : Bool
  valid : Bool
  deriving DecidableEq

def step (capacity active : ℕ) (state : State) : State :=
  match state.word with
  | [] => state
  | head :: rest =>
      if !state.inside then
        if head = .openClause then ⟨rest, true, false, state.valid⟩
        else ⟨rest, false, false, false⟩
      else if head = .closeClause then
        ⟨rest, false, false, state.valid && state.nonempty⟩
      else ⟨(fieldState capacity state.word).word, true, true,
        state.valid && (readLiteral capacity active state.word).isSome⟩

def initial (word : List Symbol) : State := ⟨word, false, false, true⟩
def accepts (state : State) : Bool := state.word.isEmpty && !state.inside && state.valid

theorem step_length (capacity active : ℕ) (state : State) :
    (step capacity active state).word.length ≤ state.word.length := by
  cases word : state.word with
  | nil => simp [step, word]
  | cons head rest =>
    simp only [step, word]
    split_ifs <;> simp only [List.length_cons]
    all_goals first | omega | simpa using field_length capacity (head :: rest)

theorem step_strict (capacity active : ℕ) (state : State) (nonempty : state.word ≠ []) :
    (step capacity active state).word.length < state.word.length := by
  cases word : state.word with
  | nil => exact False.elim (nonempty word)
  | cons head rest =>
    simp only [step, word]
    split_ifs <;> simp only [List.length_cons]
    all_goals first
      | omega
      | simp only [fieldState, NativeHeader.iterate_word, List.tail_cons, List.length_drop]; omega

theorem iterate_empty (capacity active count : ℕ) (state : State) (enough : state.word.length ≤ count) :
    ((step capacity active)^[count] state).word = [] := by
  induction count generalizing state with
  | zero => have empty := List.length_eq_zero_iff.mp (by omega : state.word.length = 0); simpa using empty
  | succ count ih =>
    by_cases empty : state.word = []
    · have fixed : step capacity active state = state := by simp [step, empty]
      simpa only [Function.iterate_succ_apply, fixed] using ih state (by simp [empty])
    · rw [Function.iterate_succ_apply]
      exact ih _ (by have := step_strict capacity active state empty; omega)

theorem step_invalid (capacity active : ℕ) (state : State) (invalid : state.valid = false) :
    (step capacity active state).valid = false := by
  cases word : state.word with
  | nil => simp [step, word, invalid]
  | cons head rest =>
    simp only [step, word]
    split <;> split <;> simp [invalid]

/-- A ghost invariant for reconstruction. All saved clauses and literals are
actual decoded syntax, while the native implementation stores only the three
control flags above. -/
def Reconstructs (capacity active : ℕ) (original : List Symbol) (state : State) : Prop :=
  state.valid = true → ∃ (done : Formula) (current : Clause),
    done.valid active ∧ (∀ lit ∈ current, lit.valid active) ∧
    (state.nonempty = true ↔ current ≠ []) ∧
    (if state.inside then
      original = done.bodyWord capacity ++ .openClause ::
        (current.flatMap (Literal.encode capacity) ++ state.word)
    else current = [] ∧ original = done.bodyWord capacity ++ state.word)

theorem initial_reconstructs (capacity active : ℕ) (word : List Symbol) :
    Reconstructs capacity active word (initial word) := by
  intro _
  exact ⟨[], [], by simp [Formula.valid], by simp, by simp [initial], by simp [initial, Formula.bodyWord]⟩

theorem valid_append_clause (active : ℕ) (done : Formula) (current : Clause)
    (good : done.valid active) (nonempty : current ≠ []) (literals : ∀ lit ∈ current, lit.valid active) :
    (done ++ [current]).valid active := by
  intro clause member
  rcases List.mem_append.mp member with member | member
  · exact good clause member
  · have same : clause = current := by simpa using member
    subst clause
    exact ⟨nonempty, literals⟩

theorem bodyWord_append (capacity : ℕ) (left right : Formula) :
    (left ++ right).bodyWord capacity = left.bodyWord capacity ++ right.bodyWord capacity := by
  simp [Formula.bodyWord]

theorem step_reconstructs (capacity active : ℕ) (original : List Symbol) (state : State)
    (invariant : Reconstructs capacity active original state) :
    Reconstructs capacity active original (step capacity active state) := by
  intro accepted
  have valid : state.valid = true := by
    cases good : state.valid with
    | true => rfl
    | false => have := step_invalid capacity active state good; simp [this] at accepted
  obtain ⟨done, current, good, literals, nonempty, reconstruct⟩ := invariant valid
  cases word : state.word with
  | nil =>
    have fixed : step capacity active state = state := by simp [step, word]
    rw [fixed] at accepted
    rw [fixed]
    exact invariant accepted
  | cons head rest =>
    by_cases inside : state.inside = true
    · have body : original = done.bodyWord capacity ++ .openClause ::
          (current.flatMap (Literal.encode capacity) ++ state.word) := by simpa [inside] using reconstruct
      by_cases close : head = .closeClause
      · have seen : state.nonempty = true := by simpa [step, word, inside, close, valid] using accepted
        refine ⟨done ++ [current], [], valid_append_clause active done current good (nonempty.mp seen) literals,
          by simp, by simp [step, word, inside, close], ?_⟩
        simpa [step, word, inside, close, bodyWord_append, Formula.bodyWord, Clause.encode,
          List.append_assoc] using body
      · have parsed : (readLiteral capacity active state.word).isSome = true := by
          simpa [step, word, inside, close, valid] using accepted
        obtain ⟨lit, decoded⟩ := Option.isSome_iff_exists.mp parsed
        obtain ⟨literalGood, encoding⟩ := readLiteral_sound capacity active state.word lit decoded
        refine ⟨done, current ++ [lit], good, ?_, ?_, ?_⟩
        · intro item member
          rcases List.mem_append.mp member with old | fresh
          · exact literals item old
          · have same : item = lit := by simpa using fresh
            simpa [same] using literalGood
        · simp [step, word, inside, close]
        · rw [encoding] at body
          simpa [step, word, inside, close, List.flatMap_append, List.append_assoc] using body
    · have outside : state.inside = false := Bool.eq_false_iff.mpr inside
      have previous : current = [] ∧ original = done.bodyWord capacity ++ state.word := by
        simpa [outside] using reconstruct
      have opening : head = .openClause := by
        by_contra bad
        simp [step, word, outside, bad] at accepted
      refine ⟨done, [], good, by simp, ?_, ?_⟩
      · simp [step, word, outside, opening]
      · simpa [step, word, outside, opening] using previous.2

theorem iterate_reconstructs (capacity active count : ℕ) (word : List Symbol) :
    Reconstructs capacity active word ((step capacity active)^[count] (initial word)) := by
  induction count with
  | zero => exact initial_reconstructs capacity active word
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    exact step_reconstructs capacity active word _ ih

theorem accepted_sound (capacity active count : ℕ) (word : List Symbol)
    (accepted : accepts ((step capacity active)^[count] (initial word)) = true) :
    ∃ formula : Formula, formula.valid active ∧ word = formula.bodyWord capacity := by
  let final := (step capacity active)^[count] (initial word)
  have tests : final.word = [] ∧ final.inside = false ∧ final.valid = true := by
    have parsed : (final.word = [] ∧ final.inside = false) ∧ final.valid = true := by
      simpa [accepts, final, Bool.and_eq_true, Bool.not_eq_true] using accepted
    exact ⟨parsed.1.1, parsed.1.2, parsed.2⟩
  obtain ⟨done, current, good, _, _, reconstruct⟩ := iterate_reconstructs capacity active count word tests.2.2
  refine ⟨done, good, ?_⟩
  change (if final.inside then word = done.bodyWord capacity ++ .openClause ::
    (current.flatMap (Literal.encode capacity) ++ final.word)
    else current = [] ∧ word = done.bodyWord capacity ++ final.word) at reconstruct
  simp only [tests.2.1, Bool.false_eq_true, ite_false, tests.1, List.append_nil] at reconstruct
  exact reconstruct.2

end ComplexityOfGenerators.Examples.PaddedCNF.NativeBody
