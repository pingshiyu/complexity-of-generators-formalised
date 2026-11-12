import ComplexityOfGenerators.Examples.SATAncestors

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

/-- On every satisfying target, the paper's constant-replacement choices
have exactly the required inverse fibre, with no assumed predecessor oracle.
The capacity and target-length tests also account for empty inverse fibres. -/
theorem inverseFibre_bit {M d n : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) (satisfiable : Satisfiable d f) (b : Bool) :
    selfReduction.inverseFibre n (f.encode M d) [bitSymbol b] =
      {word | d + 1 ≤ M ∧ (f.encode M d).length = n ∧
        ∃ choices, word = (f.lift d b choices).encode M (d + 1)} := by
  ext word
  constructor
  · rintro ⟨ancestor, reduction, labelLength⟩
    rw [ancestors_eq_slice] at ancestor
    obtain ⟨⟨M', d', g, bound', valid', sat', equal⟩, length⟩ := ancestor
    have labelWidth : wordWidth word = 1 := labelLength.symm
    have rankPositive : 0 < d' := by
      rw [← equal, wordWidth, wordRank_encode bound' g valid'] at labelWidth
      exact (width_positive d').mp (by omega)
    cases d' with
    | zero => omega
    | succ d' =>
      change wordReduce word [bitSymbol b] = f.encode M d at reduction
      rw [← equal, wordReduce_encode_bit bound' g valid'] at reduction
      have same := encode_injective (by omega : d' ≤ M') (g.valid_substitute b valid')
        bound valid reduction
      obtain ⟨capacities, parameters⟩ := Prod.mk.inj same
      obtain ⟨ranks, substituted⟩ := Prod.mk.inj parameters
      subst M'
      subst d'
      obtain ⟨choices, _, recovered⟩ := g.lift_complete b valid'
      have source : word = (f.lift d b choices).encode M (d + 1) := by
        rw [substituted] at recovered
        rw [recovered]
        exact equal.symm
      refine ⟨bound', ?_, choices, source⟩
      have sameLength := g.substitute_encoding_length bound' b valid'
      rw [substituted, equal] at sameLength
      exact sameLength.trans length
  · rintro ⟨more, length, choices, rfl⟩
    have good := f.lift_valid b valid choices
    have sat := f.lift_satisfiable b valid satisfiable choices
    have outputLength := f.lift_encoding_length more b valid choices
    refine ⟨?_, ?_, ?_⟩
    · rw [ancestors_eq_slice]
      exact ⟨⟨M, d + 1, f.lift d b choices, more, good, sat, rfl⟩,
        outputLength.trans length⟩
    · change wordReduce _ _ = _
      rw [wordReduce_encode_bit more _ good, f.substitute_lift b valid choices]
    · change 1 = wordWidth _
      simp [wordWidth, wordRank_encode more _ good, width]

theorem inverseFibre_bit_nonempty {M d n : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) (satisfiable : Satisfiable d f) (b : Bool) :
    (selfReduction.inverseFibre n (f.encode M d) [bitSymbol b]).Nonempty ↔
      d + 1 ≤ M ∧ (f.encode M d).length = n := by
  rw [inverseFibre_bit bound f valid satisfiable b]
  constructor
  · rintro ⟨_, more, length, _⟩
    exact ⟨more, length⟩
  · rintro ⟨more, length⟩
    exact ⟨(f.lift d b []).encode M (d + 1), more, length, [], rfl⟩

/-- Empty labels occur only at rank zero and reproduce their target. -/
theorem inverseFibre_empty {M d n : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) (satisfiable : Satisfiable d f) :
    selfReduction.inverseFibre n (f.encode M d) [] =
      {word | d = 0 ∧ (f.encode M d).length = n ∧ word = f.encode M d} := by
  ext word
  constructor
  · rintro ⟨ancestor, reduction, labelLength⟩
    rw [ancestors_eq_slice] at ancestor
    obtain ⟨⟨M', d', g, bound', valid', sat', encoded⟩, length⟩ := ancestor
    change wordReduce word [] = f.encode M d at reduction
    change 0 = wordWidth word at labelLength
    have zero : d' = 0 := by
      rw [← encoded, wordWidth, wordRank_encode bound' g valid'] at labelLength
      by_contra positive
      simp [width, positive] at labelLength
    subst d'
    have identity : wordReduce word [] = word := by
      simp [wordReduce, ← encoded, decode_encode bound' g valid']
    rw [identity] at reduction
    have targetRank : d = 0 := by
      have rank := wordRank_encode bound' g valid'
      rw [encoded, reduction, wordRank_encode bound f valid] at rank
      exact rank
    exact ⟨targetRank, by simpa [reduction] using length, reduction⟩
  · rintro ⟨rfl, length, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [ancestors_eq_slice]
      exact ⟨⟨M, 0, f, bound, valid, satisfiable, rfl⟩, length⟩
    · change wordReduce _ [] = _
      simp [wordReduce, decode_encode bound f valid]
    · change 0 = wordWidth _
      simp [wordWidth, wordRank_encode bound f valid, width]

end ComplexityOfGenerators.Examples.PaddedCNF
