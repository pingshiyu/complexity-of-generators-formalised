import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Value
import ComplexityOfGenerators.Examples.HAMPATHInverseWords

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
set_option backward.isDefEq.respectTransparency false

theorem empty_certificate_iff (word : List Symbol) : [] ∈ wordCertificates word ↔ word = baseWord := by
  constructor
  · intro member
    have languageMember := (word_mem_iff_certificates word).mpr ⟨[], member⟩
    obtain ⟨G, start, path, rfl⟩ := languageMember
    have zero := word_certificate_length (G.encode start) [] member
    rw [wordRank_encode G start path.start_bound, List.length_nil] at zero
    obtain ⟨rfl, rfl⟩ := rank_zero_graph G path zero.symm
    rfl
  · intro equal
    subst word
    change [] ∈ wordCertificates (singleton.encode 0)
    rw [wordCertificates_encode singleton 0 singleton_hamiltonian.start_bound]
    simp [graphCertificates, singleton]

theorem split_take_iff (word certificate : List Symbol) (enough : wordWidth word ≤ certificate.length) :
    certificate ∈ wordCertificates word ↔
      certificate.drop (wordWidth word) ∈ wordCertificates (wordReduce word (certificate.take (wordWidth word))) := by
  constructor
  · intro member
    obtain ⟨label, tail, length, good, equal⟩ := (word_split word certificate).mp member
    have front : certificate.take (wordWidth word) = label := by simp [equal, ← length]
    have rest : certificate.drop (wordWidth word) = tail := by simp [equal, ← length]
    simpa only [front, rest] using good
  · intro member
    exact (word_split word certificate).mpr ⟨_, _, by simp [Nat.min_eq_left enough], member, (List.take_append_drop _ _).symm⟩

theorem wordReduce_short (word label : List Symbol) (short : label.length < wordWidth word) : wordReduce word label = [] := by
  cases parsed : decode word with
  | none => simp [wordWidth, parsed] at short
  | some result =>
    obtain ⟨G, start⟩ := result
    have positive : 0 < width G.size := by simpa only [wordWidth, parsed] using (by omega : 0 < wordWidth word)
    have large := width_positive_size positive
    have unequal : label.length ≠ width G.size := by
      have : label.length < width G.size := by simpa only [wordWidth, parsed] using short
      omega
    simp [wordReduce, parsed, show ¬ G.size ≤ 1 by omega, decodeLabel, unequal]

theorem step_certificate_iff (state : State) :
    state.remaining ∈ wordCertificates state.current ↔ (step state).remaining ∈ wordCertificates (step state).current := by
  by_cases empty : state.remaining = []
  · simp [step, empty]
  · by_cases enough : wordWidth state.current ≤ state.remaining.length
    · simpa only [step, ite_eq_right empty] using split_take_iff state.current state.remaining enough
    · have short : (state.remaining.take (wordWidth state.current)).length < wordWidth state.current := by
        simp only [List.length_take]
        omega
      have rejected := wordReduce_short state.current _ short
      have invalid : state.remaining ∉ wordCertificates state.current := by
        intro member
        obtain ⟨label, tail, length, _, equal⟩ := (word_split state.current state.remaining).mp member
        have sizes := congrArg List.length equal
        simp only [List.length_append] at sizes
        omega
      simp [step, empty, rejected, invalid]

theorem iterate_certificate_iff (count : ℕ) (state : State) :
    state.remaining ∈ wordCertificates state.current ↔
      (step^[count] state).remaining ∈ wordCertificates (step^[count] state).current := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply]; exact (step_certificate_iff state).trans (ih _)

theorem member_remaining_decreases (state : State) (member : state.remaining ∈ wordCertificates state.current)
    (nonempty : state.remaining ≠ []) : (step state).remaining.length < state.remaining.length := by
  have length := word_certificate_length state.current state.remaining member
  have positive : 0 < wordRank state.current := by have := List.length_pos_iff.mpr nonempty; omega
  have widthPositive := (word_positive state.current).mp positive
  simp only [step, ite_eq_right nonempty, List.length_drop]
  omega

theorem member_consumed (count : ℕ) (state : State) (member : state.remaining ∈ wordCertificates state.current)
    (enough : state.remaining.length ≤ count) : (step^[count] state).remaining = [] := by
  induction count generalizing state with
  | zero =>
    change state.remaining = []
    exact List.length_eq_zero_iff.mp (by omega)
  | succ count ih =>
    by_cases empty : state.remaining = []
    · rw [iterate_empty _ state empty]
      exact empty
    · have shorter := member_remaining_decreases state member empty
      have next := (step_certificate_iff state).mp member
      rw [Function.iterate_succ_apply]
      exact ih _ next (by omega)

/-- The finite consuming algorithm checks exactly the concrete path-block
certificate relation, on malformed words and labels as well as valid graphs. -/
theorem value_iff_certificate (word certificate : List Symbol) :
    value word certificate = true ↔ certificate ∈ wordCertificates word := by
  let final := step^[certificate.length] (⟨word, certificate⟩ : State)
  have preserves := iterate_certificate_iff certificate.length (⟨word, certificate⟩ : State)
  constructor
  · intro accepted
    have fields : final.remaining = [] ∧ final.current = baseWord := by simpa [value, accepts, final] using accepted
    have good := (empty_certificate_iff final.current).mpr fields.2
    rw [← fields.1] at good
    exact preserves.mpr good
  · intro member
    have empty : final.remaining = [] := member_consumed certificate.length _ member le_rfl
    have good := preserves.mp member
    change final.remaining ∈ wordCertificates final.current at good
    rw [empty] at good
    have base := (empty_certificate_iff final.current).mp good
    change accepts final = true
    simp [accepts, empty, base]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
