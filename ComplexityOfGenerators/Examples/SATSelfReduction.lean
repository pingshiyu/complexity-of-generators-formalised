import ComplexityOfGenerators.Examples.SATWordReduction

/-!
The padded-CNF construction is a self-reduction of the actual word language.
Malformed words and nonbinary certificate labels have empty certificate sets;
at rank zero the empty label acts as the identity. Computational native-machine
witnesses are deliberately separate from this semantic construction.
-/

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

theorem symbol_bitValue {s : Symbol} (binary : s = .zero ∨ s = .one) :
    bitSymbol (bitValue s) = s := by rcases binary with rfl | rfl <;> rfl

theorem binary_cons (s : Symbol) (tail : List Symbol) :
    Binary (s :: tail) ↔ (s = .zero ∨ s = .one) ∧ Binary tail := by
  simp only [Binary, List.mem_cons]
  constructor
  · intro binary
    exact ⟨binary s (Or.inl rfl), fun t ht => binary t (Or.inr ht)⟩
  · rintro ⟨head, tail⟩ t (rfl | member)
    · exact head
    · exact tail t member

theorem bool_certificate_cons (d : ℕ) (f : Formula) (b : Bool) (tail : List Bool) :
    b :: tail ∈ certificates (d + 1) f ↔
      tail ∈ certificates d (f.substitute (d + 1) b) := by
  rw [certificate_prefix]
  constructor
  · rintro ⟨b', tail', equal, good⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj equal
    exact good
  · intro good
    exact ⟨b, tail, rfl, good⟩

theorem word_certificate_cons {M d : ℕ} (bound : d + 1 ≤ M) (f : Formula)
    (valid : f.valid (d + 1)) (s : Symbol) (tail : List Symbol) :
    s :: tail ∈ wordCertificates (f.encode M (d + 1)) ↔
      ∃ b, s = bitSymbol b ∧
        tail ∈ wordCertificates ((f.substitute (d + 1) b).encode M d) := by
  rw [wordCertificates_encode bound f valid]
  simp only [Set.mem_ofPred_eq, binary_cons, List.map_cons, bool_certificate_cons]
  constructor
  · rintro ⟨⟨head, binary⟩, good⟩
    refine ⟨bitValue s, (symbol_bitValue head).symm, ?_⟩
    rw [wordCertificates_encode (by omega : d ≤ M) _ (f.valid_substitute _ valid)]
    exact ⟨binary, good⟩
  · rintro ⟨b, rfl, good⟩
    rw [wordCertificates_encode (by omega : d ≤ M) _ (f.valid_substitute _ valid)] at good
    refine ⟨⟨?_, good.1⟩, ?_⟩
    · cases b <;> simp [bitSymbol]
    · simpa using good.2

theorem word_split_positive {M d : ℕ} (bound : d + 1 ≤ M) (f : Formula)
    (valid : f.valid (d + 1)) (certificate : List Symbol) :
    certificate ∈ wordCertificates (f.encode M (d + 1)) ↔
      ∃ label tail, label.length = 1 ∧
        tail ∈ wordCertificates (wordReduce (f.encode M (d + 1)) label) ∧
        certificate = label ++ tail := by
  constructor
  · intro good
    cases certificate with
    | nil =>
      have := word_certificate_length (f.encode M (d + 1)) [] good
      rw [wordRank_encode bound f valid] at this
      simp at this
    | cons s tail =>
      obtain ⟨b, rfl, tailGood⟩ := (word_certificate_cons bound f valid s tail).mp good
      refine ⟨[bitSymbol b], tail, rfl, ?_, rfl⟩
      rw [wordReduce_encode_bit bound f valid]
      exact tailGood
  · rintro ⟨label, tail, length, good, rfl⟩
    have single : ∃ s, label = [s] := by
      cases label with
      | nil => simp at length
      | cons s rest =>
        have empty : rest = [] := List.length_eq_zero_iff.mp (by simpa using length)
        exact ⟨s, by rw [empty]⟩
    obtain ⟨s, rfl⟩ := single
    cases bit : labelValue [s] with
    | none =>
      simp [wordReduce, decode_encode bound f valid, bit] at good
    | some b =>
      have symbol : s = bitSymbol b := by
        cases s <;> cases b <;> simp_all [labelValue, bitSymbol]
      subst s
      change bitSymbol b :: tail ∈ wordCertificates (f.encode M (d + 1))
      rw [wordReduce_encode_bit bound f valid] at good
      exact (word_certificate_cons bound f valid _ tail).mpr ⟨b, rfl, good⟩

theorem word_split (word certificate : List Symbol) :
    certificate ∈ wordCertificates word ↔
      ∃ label tail, label.length = wordWidth word ∧
        tail ∈ wordCertificates (wordReduce word label) ∧ certificate = label ++ tail := by
  cases decoded : decode word with
  | none => simp [wordCertificates, wordReduce, decoded]
  | some result =>
    rcases result with ⟨M, d, f⟩
    obtain ⟨bound, valid, equal⟩ := decode_sound word M d f decoded
    cases d with
    | zero =>
      have zeroRank : wordRank word = 0 := by rw [← equal, wordRank_encode bound f valid]
      have zeroWidth : wordWidth word = 0 := by simp [wordWidth, zeroRank, width]
      rw [zeroWidth]
      constructor
      · intro good
        refine ⟨[], certificate, rfl, ?_, rfl⟩
        simpa [wordReduce, decoded] using good
      · rintro ⟨label, tail, length, good, rfl⟩
        have empty : label = [] := List.length_eq_zero_iff.mp length
        subst label
        simpa [wordReduce, decoded] using good
    | succ d =>
      have rank : wordRank word = d + 1 := by rw [← equal, wordRank_encode bound f valid]
      have width : wordWidth word = 1 := by simp [wordWidth, rank, PaddedCNF.width]
      rw [width, ← equal]
      exact word_split_positive bound f valid certificate

/-- The manuscript's padded SAT encoding, including all malformed-word cases,
satisfies the full certificate equation and quantitative self-reduction laws. -/
def selfReduction : SelfReduction language where
  certificates := wordCertificates
  rank := wordRank
  width := wordWidth
  reduce := wordReduce
  certifies := word_mem_iff_certificates
  certificate_length := word_certificate_length
  split := word_split
  positive := by intro word; exact (width_positive (wordRank word)).symm
  length_reduce := word_reduce_length
  rank_reduce := word_reduce_rank
  rankBound := ⟨1, 1, by omega⟩
  rank_le := by intro word; simpa [PolynomialBound.eval] using (word_rank_bound word).trans (Nat.le_succ _)
  logCoefficient := 0
  logConstant := 1
  width_le := by intro word; simpa using word_width_bound word

end ComplexityOfGenerators.Examples.PaddedCNF
