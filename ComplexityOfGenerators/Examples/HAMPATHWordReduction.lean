import ComplexityOfGenerators.Examples.HAMPATHCertificates
import ComplexityOfGenerators.Examples.HAMPATHParser

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

def wordCertificates (word : List Symbol) : Set (List Symbol) :=
  match decode word with
  | none => ∅
  | some (G, start) => graphCertificates G start

def wordRank (word : List Symbol) : ℕ :=
  match decode word with
  | none => 0
  | some (G, _) => rank G.size

def wordWidth (word : List Symbol) : ℕ :=
  match decode word with
  | none => 0
  | some (G, _) => width G.size

def wordReduce (word label : List Symbol) : List Symbol :=
  match decode word with
  | none => []
  | some (G, start) =>
      if G.size ≤ 1 then if label = [] then word else []
      else match decodeLabel G.size label with
        | none => []
        | some next =>
            if next ≠ start ∧ G.edge start next = true then
              (G.delete start).encode (contract start next)
            else []

@[simp] theorem decode_nil : decode [] = none := rfl
@[simp] theorem wordRank_nil : wordRank [] = 0 := rfl
@[simp] theorem wordWidth_nil : wordWidth [] = 0 := rfl
@[simp] theorem wordCertificates_nil : wordCertificates [] = ∅ := rfl

theorem wordCertificates_encode (G : Graph) (start : ℕ) (inside : start < G.size) :
    wordCertificates (G.encode start) = graphCertificates G start := by
  simp [wordCertificates, decode_encode G start inside]

theorem wordRank_encode (G : Graph) (start : ℕ) (inside : start < G.size) :
    wordRank (G.encode start) = rank G.size := by simp [wordRank, decode_encode G start inside]

theorem wordWidth_encode (G : Graph) (start : ℕ) (inside : start < G.size) :
    wordWidth (G.encode start) = width G.size := by simp [wordWidth, decode_encode G start inside]

theorem word_mem_iff_certificates (word : List Symbol) :
    word ∈ language ↔ (wordCertificates word).Nonempty := by
  constructor
  · rintro ⟨G, start, member, rfl⟩
    rw [wordCertificates_encode G start member.start_bound]
    exact (graph_certifies G start).mp member
  · intro nonempty
    cases parsed : decode word with
    | none => simp [wordCertificates, parsed] at nonempty
    | some result =>
      obtain ⟨G, start⟩ := result
      have good : (graphCertificates G start).Nonempty := by
        simpa [wordCertificates, parsed] using nonempty
      exact ⟨G, start, (graph_certifies G start).mpr good, (decode_sound parsed).2⟩

theorem word_certificate_length (word certificate : List Symbol)
    (member : certificate ∈ wordCertificates word) : certificate.length = wordRank word := by
  cases parsed : decode word with
  | none => simp [wordCertificates, parsed] at member
  | some result =>
    obtain ⟨G, start⟩ := result
    have good : certificate ∈ graphCertificates G start := by
      simpa [wordCertificates, parsed] using member
    simpa [wordRank, parsed] using graph_certificate_length G start certificate good

theorem word_positive (word : List Symbol) : 0 < wordRank word ↔ 0 < wordWidth word := by
  cases parsed : decode word with
  | none => simp [wordRank, wordWidth, parsed]
  | some result => obtain ⟨G, start⟩ := result; simpa [wordRank, wordWidth, parsed] using rank_positive_iff G.size

theorem word_rank_bound (word : List Symbol) : wordRank word ≤ word.length := by
  cases parsed : decode word with
  | none => simp [wordRank, parsed]
  | some result =>
    obtain ⟨G, start⟩ := result
    have equal := (decode_sound parsed).2
    simp only [wordRank, parsed]
    rw [← equal, G.encode_length]
    exact rank_encoding_bound G.size

theorem word_width_log_bound (word : List Symbol) :
    wordWidth word ≤ Nat.log 2 (word.length + 1) + 1 := by
  cases parsed : decode word with
  | none => simp [wordWidth, parsed]
  | some result =>
    obtain ⟨G, start⟩ := result
    have equal := (decode_sound parsed).2
    simp only [wordWidth, parsed]
    rw [← equal, G.encode_length]
    exact (width_encoding_log_bound G.size).trans
      (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 1)

theorem wordReduce_encode_label (G : Graph) (start next : ℕ) (inside : start < G.size)
    (large : 2 ≤ G.size) (nextBound : next < G.size) (different : next ≠ start)
    (edge : G.edge start next = true) :
    wordReduce (G.encode start) (vertexLabel G.size next) =
      (G.delete start).encode (contract start next) := by
  simp [wordReduce, decode_encode G start inside, show ¬ G.size ≤ 1 by omega,
    decodeLabel_encode nextBound, different, edge]

theorem word_reduce_length (word label : List Symbol) :
    (wordReduce word label).length ≤ word.length := by
  cases parsed : decode word with
  | none => simp [wordReduce, parsed]
  | some result =>
    obtain ⟨G, start⟩ := result
    obtain ⟨inside, equal⟩ := decode_sound parsed
    by_cases small : G.size ≤ 1
    · by_cases empty : label = [] <;> simp [wordReduce, parsed, small, empty]
    · cases decoded : decodeLabel G.size label with
      | none => simp [wordReduce, parsed, small, decoded]
      | some next =>
        by_cases good : next ≠ start ∧ G.edge start next = true
        · have reduced : wordReduce word label = (G.delete start).encode (contract start next) := by
            simp [wordReduce, parsed, small, decoded, good.1, good.2]
          rw [reduced]
          rw [Graph.encode_length, ← equal, Graph.encode_length]
          have size : G.size - 1 ≤ G.size := Nat.sub_le _ _
          have square := Nat.mul_le_mul size size
          simp only [Graph.delete, encodingLength]
          omega
        · simp [wordReduce, parsed, small, decoded, good]

theorem word_reduce_rank (word label : List Symbol) :
    wordRank (wordReduce word label) ≤ wordRank word - wordWidth word := by
  cases parsed : decode word with
  | none => simp [wordReduce, wordRank, wordWidth, parsed]
  | some result =>
    obtain ⟨G, start⟩ := result
    obtain ⟨inside, equal⟩ := decode_sound parsed
    by_cases small : G.size ≤ 1
    · have singletonSize : G.size = 1 := by omega
      by_cases empty : label = [] <;>
        simp [wordReduce, parsed, empty, wordRank, wordWidth,
          singletonSize, width, Nat.clog_one_right]
    · cases decoded : decodeLabel G.size label with
      | none => simp [wordReduce, parsed, small, decoded]
      | some next =>
        by_cases good : next ≠ start ∧ G.edge start next = true
        · have nextBound := (decodeLabel_sound G.size label next decoded).1
          have contracted := contract_lt_pred inside nextBound good.1
          have reduced : wordReduce word label = (G.delete start).encode (contract start next) := by
            simp [wordReduce, parsed, small, decoded, good.1, good.2]
          rw [reduced, wordRank_encode (G.delete start) _ contracted]
          simp only [wordRank, wordWidth, parsed, Graph.delete]
          exact (rank_delete G.size (by omega)).le
        · simp [wordReduce, parsed, small, decoded, good]

end ComplexityOfGenerators.Examples.HAMPATH
