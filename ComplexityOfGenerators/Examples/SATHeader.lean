import ComplexityOfGenerators.Examples.SATParserFormula

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

/-- Extend rank to malformed words by reading just the two unary header
fields. This agrees with the active-variable count on every valid encoding. -/
def headerRank (word : List Symbol) : ℕ := (readOnes (readOnes word).2.tail).1

def headerWidth (word : List Symbol) : ℕ := width (headerRank word)

theorem readOnes_lengths (word : List Symbol) :
    (readOnes word).1 + (readOnes word).2.length = word.length := by
  have lengths := congrArg List.length (readOnes_reconstruct word)
  simpa using lengths

theorem headerRank_le (word : List Symbol) : headerRank word ≤ word.length := by
  have first := readOnes_lengths word
  have second := readOnes_lengths (readOnes word).2.tail
  have tail : (readOnes word).2.tail.length ≤ (readOnes word).2.length := by
    simp only [List.length_tail]
    omega
  unfold headerRank
  omega

theorem readOnes_marks_nonone (marks : ℕ) (s : Symbol) (rest : List Symbol) (other : s ≠ .one) :
    readOnes (List.replicate marks .one ++ s :: rest) = (marks, s :: rest) := by
  induction marks with
  | zero => cases s <;> simp_all [readOnes]
  | succ marks ih => simp [List.replicate_succ, readOnes, ih]

theorem headerRank_encode (M d : ℕ) (f : Formula) : headerRank (f.encode M d) = d := by
  unfold headerRank
  have header : f.encode M d = List.replicate M .one ++ .separator ::
      (List.replicate d .one ++ List.replicate (M - d) .zero ++ .separator :: f.bodyWord M) := by
    simp [Formula.encode, Formula.bodyWord, List.append_assoc]
  rw [header, readOnes_header]
  simp only [List.tail_cons]
  cases zeros : M - d with
  | zero => simp [readOnes_header]
  | succ zeros =>
    rw [List.replicate_succ]
    simp only [List.append_assoc, List.cons_append]
    rw [readOnes_marks_nonone d .zero _ (by decide)]

end ComplexityOfGenerators.Examples.PaddedCNF
