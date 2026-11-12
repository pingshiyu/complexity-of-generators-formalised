import ComplexityOfGenerators.Examples.HAMPATHWordReduction

/-! The actual adjacency-matrix word language satisfies the complete semantic
self-reduction definition, using fixed-width binary next-vertex blocks. -/

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

theorem word_split_large (G : Graph) (start : ℕ) (inside : start < G.size)
    (large : 2 ≤ G.size) (certificate : List Symbol) :
    certificate ∈ wordCertificates (G.encode start) ↔
      ∃ label tail, label.length = width G.size ∧
        tail ∈ wordCertificates (wordReduce (G.encode start) label) ∧
        certificate = label ++ tail := by
  rw [wordCertificates_encode G start inside, graph_certificate_split G start large]
  constructor
  · rintro ⟨startBound, next, tail, nextBound, different, edge, good, equal⟩
    refine ⟨vertexLabel G.size next, tail, vertexLabel_length _ _, ?_, equal⟩
    rw [wordReduce_encode_label G start next inside large nextBound different edge,
      wordCertificates_encode _ _ (contract_lt_pred startBound nextBound different)]
    exact good
  · rintro ⟨label, tail, _, good, equal⟩
    cases decoded : decodeLabel G.size label with
    | none =>
      simp [wordReduce, decode_encode G start inside, show ¬ G.size ≤ 1 by omega,
        decoded] at good
    | some next =>
      by_cases admissible : next ≠ start ∧ G.edge start next = true
      · obtain ⟨nextBound, labelEq⟩ := decodeLabel_sound G.size label next decoded
        subst label
        rw [wordReduce_encode_label G start next inside large nextBound admissible.1 admissible.2,
          wordCertificates_encode _ _ (contract_lt_pred inside nextBound admissible.1)] at good
        exact ⟨inside, next, tail, nextBound, admissible.1, admissible.2, good, equal⟩
      · simp [wordReduce, decode_encode G start inside, show ¬ G.size ≤ 1 by omega,
          decoded, admissible] at good

theorem word_split (word certificate : List Symbol) :
    certificate ∈ wordCertificates word ↔
      ∃ label tail, label.length = wordWidth word ∧
        tail ∈ wordCertificates (wordReduce word label) ∧ certificate = label ++ tail := by
  cases parsed : decode word with
  | none => simp [wordCertificates, wordReduce, parsed]
  | some result =>
    obtain ⟨G, start⟩ := result
    obtain ⟨inside, equal⟩ := decode_sound parsed
    by_cases small : G.size ≤ 1
    · have singletonSize : G.size = 1 := by omega
      have zeroWidth : wordWidth word = 0 := by
        simp [wordWidth, parsed, singletonSize, width, Nat.clog_one_right]
      rw [zeroWidth]
      constructor
      · intro good
        refine ⟨[], certificate, rfl, ?_, rfl⟩
        simpa [wordReduce, parsed, small] using good
      · rintro ⟨label, tail, length, good, rfl⟩
        have empty : label = [] := List.length_eq_zero_iff.mp length
        subst label
        simpa [wordReduce, parsed, small] using good
    · have wordWidth : wordWidth word = width G.size := by simp [wordWidth, parsed]
      rw [wordWidth, ← equal]
      exact word_split_large G start inside (by omega) certificate

/-- This construction discharges every semantic field for the concrete paper
encoding. Native polynomial verifiers and generators are separate obligations. -/
def selfReduction : SelfReduction language where
  certificates := wordCertificates
  rank := wordRank
  width := wordWidth
  reduce := wordReduce
  certifies := word_mem_iff_certificates
  certificate_length := word_certificate_length
  split := word_split
  positive := word_positive
  length_reduce := word_reduce_length
  rank_reduce := word_reduce_rank
  rankBound := ⟨1, 1, by omega⟩
  rank_le := by intro word; simpa [PolynomialBound.eval] using (word_rank_bound word).trans (Nat.le_succ _)
  logCoefficient := 1
  logConstant := 1
  width_le := by intro word; simpa using word_width_log_bound word

end ComplexityOfGenerators.Examples.HAMPATH
