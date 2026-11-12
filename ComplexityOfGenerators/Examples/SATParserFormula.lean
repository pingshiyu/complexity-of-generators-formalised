import ComplexityOfGenerators.Examples.SATParserWords

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

def Formula.bodyWord (M : ℕ) (f : Formula) : List Symbol := f.flatMap (Clause.encode M)

def decodeFormulaFuel (M : ℕ) : ℕ → List Symbol → Option Formula
  | 0, input => if input = [] then some [] else none
  | _ + 1, [] => some []
  | fuel + 1, .openClause :: input => do
      let (payload, remaining) ← splitClose input
      let clause ← decodeBody M payload
      if clause = [] then none else do
        let rest ← decodeFormulaFuel M fuel remaining
        pure (clause :: rest)
  | _ + 1, _ => none

def decodeFormula (M : ℕ) (input : List Symbol) : Option Formula :=
  decodeFormulaFuel M input.length input

theorem Formula.bodyWord_length_ge (M : ℕ) (f : Formula) :
    f.length ≤ (f.bodyWord M).length := by
  induction f with
  | nil => simp [bodyWord]
  | cons c rest ih =>
    change rest.length + 1 ≤ (c.encode M ++ Formula.bodyWord M rest).length
    have headBound : 2 ≤ (c.encode M).length := by simp [Clause.encode]
    rw [List.length_append]
    omega

theorem decodeFormulaFuel_encode (M fuel : ℕ) (f : Formula)
    (valid : f.valid M) (enough : f.length ≤ fuel) :
    decodeFormulaFuel M fuel (f.bodyWord M) = some f := by
  induction f generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons c rest ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have tail := ih fuel (by intro c hc; exact valid c (by simp [hc])) (by simpa using enough)
      have nonempty := (valid c (by simp)).1
      have literals := (valid c (by simp)).2
      have split := splitClose_encode (c.flatMap (Literal.encode M)) (Formula.bodyWord M rest)
        (c.no_close M)
      have decode := decodeBody_encode M c literals
      have inputEq : Formula.bodyWord M (c :: rest) = .openClause ::
          (c.flatMap (Literal.encode M) ++ .closeClause :: Formula.bodyWord M rest) := by
        simp [Formula.bodyWord, Clause.encode, List.append_assoc]
      rw [inputEq]
      simp only [decodeFormulaFuel]
      rw [split]
      simp [decode, nonempty, tail]

theorem decodeFormula_encode (M : ℕ) (f : Formula) (valid : f.valid M) :
    decodeFormula M (f.bodyWord M) = some f :=
  decodeFormulaFuel_encode M _ f valid (f.bodyWord_length_ge M)

instance Literal.decidableValid (d : ℕ) (lit : Literal) : Decidable (lit.valid d) := by
  cases lit <;> unfold Literal.valid <;> infer_instance

instance Formula.decidableValid (d : ℕ) (f : Formula) : Decidable (f.valid d) := by
  unfold Formula.valid
  infer_instance

/-- Parse the capacity header, the fixed-width active-count field, and then
the bracket-delimited literal blocks. All validation is constructive. -/
def parse (input : List Symbol) : Option (ℕ × ℕ × Formula) :=
  let (M, remaining) := readOnes input
  match remaining with
  | .separator :: remaining =>
      let flags := remaining.take M
      let d := (readOnes flags).1
      if d ≤ M ∧ flags = List.replicate d .one ++ List.replicate (M - d) .zero then
        match remaining.drop M with
        | .separator :: body => do
            let formula ← decodeFormula M body
            some (M, d, formula)
        | _ => none
      else none
  | _ => none

theorem Formula.valid_mono {d M : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) : f.valid M := by
  intro c hc
  refine ⟨(valid c hc).1, ?_⟩
  intro lit hl
  have good := (valid c hc).2 lit hl
  cases lit with
  | constant value => trivial
  | var j sign => exact ⟨good.1, good.2.trans bound⟩

theorem parse_encode {M d : ℕ} (bound : d ≤ M) (f : Formula) (valid : f.valid d) :
    parse (f.encode M d) = some (M, d, f) := by
  let flags := List.replicate d Symbol.one ++ List.replicate (M - d) Symbol.zero
  have length : flags.length = M := by simp [flags]; omega
  have header : f.encode M d = List.replicate M .one ++
      .separator :: (flags ++ .separator :: f.bodyWord M) := by
    simp [Formula.encode, Formula.bodyWord, flags, List.append_assoc]
  have front : (flags ++ .separator :: f.bodyWord M).take M = flags := by
    rw [← length]; simp
  have back : (flags ++ .separator :: f.bodyWord M).drop M = .separator :: f.bodyWord M := by
    rw [← length]; simp
  rw [header]
  unfold parse
  rw [readOnes_header]
  dsimp only
  rw [front, back]
  have readFlags : readOnes flags = (d, List.replicate (M - d) Symbol.zero) :=
    readOnes_marks_zeros d (M - d)
  rw [readFlags]
  simp [flags, bound, decodeFormula_encode M f (f.valid_mono bound valid)]

/-- A constructive checked parser. Re-encoding validates the whole word,
including malformed headers and trailing junk, without an existence oracle. -/
def decode (input : List Symbol) : Option (ℕ × ℕ × Formula) := do
  let (M, d, f) ← parse input
  if d ≤ M ∧ f.valid d ∧ f.encode M d = input then some (M, d, f) else none

theorem decode_encode {M d : ℕ} (bound : d ≤ M) (f : Formula) (valid : f.valid d) :
    decode (f.encode M d) = some (M, d, f) := by
  simp [decode, parse_encode bound f valid, bound, valid]

theorem decode_sound (input : List Symbol) (M d : ℕ) (f : Formula)
    (decoded : decode input = some (M, d, f)) :
    d ≤ M ∧ f.valid d ∧ f.encode M d = input := by
  unfold decode at decoded
  cases parsed : parse input with
  | none => simp [parsed] at decoded
  | some result =>
    rcases result with ⟨M', d', f'⟩
    rw [parsed] at decoded
    change (if d' ≤ M' ∧ f'.valid d' ∧ f'.encode M' d' = input
      then some (M', d', f') else none) = some (M, d, f) at decoded
    split_ifs at decoded with good
    have equal : (M, d, f) = (M', d', f') := (Option.some.inj decoded).symm
    cases equal
    exact good

theorem encode_injective {M d M' d' : ℕ} {f f' : Formula}
    (bound : d ≤ M) (valid : f.valid d) (bound' : d' ≤ M') (valid' : f'.valid d')
    (equal : f.encode M d = f'.encode M' d') : (M, d, f) = (M', d', f') := by
  have same := congrArg decode equal
  rw [decode_encode bound f valid, decode_encode bound' f' valid'] at same
  exact Option.some.inj same

end ComplexityOfGenerators.Examples.PaddedCNF
