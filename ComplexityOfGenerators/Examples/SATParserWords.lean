import ComplexityOfGenerators.Examples.SATParser

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

def decodeLiterals (M : ℕ) : ℕ → List Symbol → Option Clause
  | 0, input => if input = [] then some [] else none
  | count + 1, input => do
      let lit ← Literal.decode M (input.take (M + 1))
      let rest ← decodeLiterals M count (input.drop (M + 1))
      pure (lit :: rest)

theorem decodeLiterals_encode (M : ℕ) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid M) :
    decodeLiterals M c.length (c.flatMap (Literal.encode M)) = some c := by
  induction c with
  | nil => rfl
  | cons lit rest ih =>
    have headLength := lit.encode_length (le_refl M) (valid lit (by simp))
    have front : (lit.encode M ++ rest.flatMap (Literal.encode M)).take (M + 1) =
        lit.encode M := by rw [← headLength]; simp
    have back : (lit.encode M ++ rest.flatMap (Literal.encode M)).drop (M + 1) =
        rest.flatMap (Literal.encode M) := by rw [← headLength]; simp
    have tail := ih (by intro l hl; exact valid l (by simp [hl]))
    simp [decodeLiterals, List.flatMap_cons, front, back, tail,
      lit.decode_encode M (valid lit (by simp))]

theorem decodeLiterals_sound (M count : ℕ) (input : List Symbol) (c : Clause)
    (decoded : decodeLiterals M count input = some c) :
    (∀ lit ∈ c, lit.valid M) ∧ c.flatMap (Literal.encode M) = input := by
  induction count generalizing input c with
  | zero =>
    simp only [decodeLiterals] at decoded
    split_ifs at decoded with empty
    have clause : c = [] := (Option.some.inj decoded).symm
    subst c
    exact ⟨by simp, empty.symm⟩
  | succ count ih =>
    cases head : Literal.decode M (input.take (M + 1)) with
    | none => simp [decodeLiterals, head] at decoded
    | some lit =>
      cases tail : decodeLiterals M count (input.drop (M + 1)) with
      | none => simp [decodeLiterals, head, tail] at decoded
      | some rest =>
        have clause : c = lit :: rest := by simpa [decodeLiterals, head, tail] using decoded.symm
        subst c
        obtain ⟨goodHead, encHead⟩ := Literal.decode_sound M _ lit head
        obtain ⟨goodTail, encTail⟩ := ih _ _ tail
        constructor
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact goodHead
          · exact goodTail l hl
        · simp [List.flatMap_cons, encHead, encTail]

theorem literalWords_length (M : ℕ) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid M) :
    (c.flatMap (Literal.encode M)).length = (M + 1) * c.length := by
  induction c with
  | nil => simp
  | cons lit rest ih =>
    have tail := ih (by intro l hl; exact valid l (by simp [hl]))
    simp [List.flatMap_cons, lit.encode_length (le_refl M) (valid lit (by simp)),
      tail, Nat.mul_add]
    omega

def decodeBody (M : ℕ) (input : List Symbol) : Option Clause :=
  decodeLiterals M (input.length / (M + 1)) input

theorem decodeBody_encode (M : ℕ) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid M) :
    decodeBody M (c.flatMap (Literal.encode M)) = some c := by
  unfold decodeBody
  rw [literalWords_length M c valid]
  simpa using decodeLiterals_encode M c valid

/-- Find the first closing bracket, retaining exactly the unconsumed suffix. -/
def splitClose : List Symbol → Option (List Symbol × List Symbol)
  | [] => none
  | .closeClause :: rest => some ([], rest)
  | symbol :: rest => do
      let (payload, remaining) ← splitClose rest
      pure (symbol :: payload, remaining)

theorem splitClose_cons (symbol : Symbol) (rest : List Symbol)
    (different : symbol ≠ .closeClause) :
    splitClose (symbol :: rest) = (splitClose rest).map (fun result =>
      (symbol :: result.1, result.2)) := by
  cases symbol <;> simp_all only [ne_eq, not_true_eq_false, splitClose]
  all_goals
    cases splitClose rest with
    | none => rfl
    | some result => rcases result with ⟨front, back⟩; rfl

theorem splitClose_encode (payload rest : List Symbol)
    (noClose : Symbol.closeClause ∉ payload) :
    splitClose (payload ++ .closeClause :: rest) = some (payload, rest) := by
  induction payload with
  | nil => rfl
  | cons symbol tail ih =>
    have notClose : symbol ≠ .closeClause := by intro eq; exact noClose (by simp [eq])
    have tail := ih (by intro member; exact noClose (by simp [member]))
    cases symbol <;> simp_all [splitClose]

theorem splitClose_sound (input payload rest : List Symbol)
    (split : splitClose input = some (payload, rest)) :
    payload ++ .closeClause :: rest = input := by
  induction input generalizing payload rest with
  | nil => simp [splitClose] at split
  | cons symbol remaining ih =>
    by_cases close : symbol = .closeClause
    · subst symbol
      have equal : (payload, rest) = ([], remaining) := by simpa [splitClose] using split.symm
      cases equal
      rfl
    · rw [splitClose_cons symbol remaining close] at split
      cases next : splitClose remaining with
      | none => simp [next] at split
      | some result =>
        rcases result with ⟨front, back⟩
        have equal : (payload, rest) = (symbol :: front, back) := by
          simpa [next] using split.symm
        have payloadEq : payload = symbol :: front := congrArg Prod.fst equal
        have restEq : rest = back := congrArg Prod.snd equal
        rw [payloadEq, restEq]
        simpa using congrArg (symbol :: ·) (ih front back next)

theorem Literal.no_close (M : ℕ) (lit : Literal) :
    Symbol.closeClause ∉ lit.encode M := by
  cases lit with
  | constant b => cases b <;> simp [encode]
  | var j sign => cases sign <;> simp [encode]

theorem Clause.no_close (M : ℕ) (c : Clause) :
    Symbol.closeClause ∉ c.flatMap (Literal.encode M) := by
  intro member
  obtain ⟨lit, _, inside⟩ := List.mem_flatMap.mp member
  exact lit.no_close M inside

end ComplexityOfGenerators.Examples.PaddedCNF
