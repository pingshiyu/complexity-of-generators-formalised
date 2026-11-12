import ComplexityOfGenerators.Examples.SATHeader

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

def bitSymbol : Bool → Symbol
  | false => .zero
  | true => .one

def bitValue : Symbol → Bool
  | .one => true
  | _ => false

@[simp] theorem bitValue_symbol (b : Bool) : bitValue (bitSymbol b) = b := by cases b <;> rfl

def Binary (c : List Symbol) : Prop := ∀ s ∈ c, s = .zero ∨ s = .one

theorem binary_encoded (c : List Bool) : Binary (c.map bitSymbol) := by
  intro s hs
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
  cases b <;> simp [bitSymbol]

@[simp] theorem bits_encoded (c : List Bool) : (c.map bitSymbol).map bitValue = c := by
  simp [List.map_map, Function.comp_def]

def wordCertificates (word : List Symbol) : Set (List Symbol) :=
  match decode word with
  | none => ∅
  | some (_, d, f) => {c | Binary c ∧ c.map bitValue ∈ certificates d f}

def wordRank (word : List Symbol) : ℕ := headerRank word

def wordWidth (word : List Symbol) : ℕ := width (wordRank word)

@[simp] theorem decode_nil : decode [] = none := rfl

@[simp] theorem wordRank_nil : wordRank [] = 0 := rfl

@[simp] theorem wordCertificates_nil : wordCertificates [] = ∅ := rfl

theorem wordCertificates_encode {M d : ℕ} (bound : d ≤ M) (f : Formula) (valid : f.valid d) :
    wordCertificates (f.encode M d) = {c | Binary c ∧ c.map bitValue ∈ certificates d f} := by
  simp only [wordCertificates, decode_encode bound f valid]

theorem wordRank_encode {M d : ℕ} (_bound : d ≤ M) (f : Formula) (_valid : f.valid d) :
    wordRank (f.encode M d) = d := headerRank_encode M d f

theorem word_mem_iff_certificates (word : List Symbol) :
    word ∈ language ↔ (wordCertificates word).Nonempty := by
  constructor
  · rintro ⟨M, d, f, bound, valid, ⟨certificate, good⟩, rfl⟩
    rw [wordCertificates_encode bound f valid]
    exact ⟨certificate.map bitSymbol, binary_encoded certificate,
      by rw [bits_encoded]; exact good⟩
  · intro nonempty
    cases decoded : decode word with
    | none => simp [wordCertificates, decoded] at nonempty
    | some result =>
      rcases result with ⟨M, d, f⟩
      obtain ⟨bound, valid, equal⟩ := decode_sound word M d f decoded
      have witnesses : ({c | Binary c ∧ c.map bitValue ∈ certificates d f} :
          Set (List Symbol)).Nonempty := by simpa [wordCertificates, decoded] using nonempty
      obtain ⟨certificate, _, good⟩ := witnesses
      exact ⟨M, d, f, bound, valid, ⟨certificate.map bitValue, good⟩, equal⟩

theorem word_certificate_length (word certificate : List Symbol)
    (good : certificate ∈ wordCertificates word) : certificate.length = wordRank word := by
  cases decoded : decode word with
  | none => simp [wordCertificates, decoded] at good
  | some result =>
    rcases result with ⟨M, d, f⟩
    obtain ⟨bound, valid, equal⟩ := decode_sound word M d f decoded
    have length : (certificate.map bitValue).length = d := by
      have member : certificate.map bitValue ∈ certificates d f :=
        (show Binary certificate ∧ certificate.map bitValue ∈ certificates d f from
          by simpa [wordCertificates, decoded] using good).2
      exact member.1
    rw [← equal, wordRank_encode bound f valid]
    simpa using length

theorem word_rank_bound (word : List Symbol) : wordRank word ≤ word.length := headerRank_le word

theorem word_width_bound (word : List Symbol) : wordWidth word ≤ 1 := by
  unfold wordWidth width
  split <;> omega

def labelValue : List Symbol → Option Bool
  | [.zero] => some false
  | [.one] => some true
  | _ => none

@[simp] theorem labelValue_bit (b : Bool) : labelValue [bitSymbol b] = some b := by
  cases b <;> rfl

def wordReduce (word label : List Symbol) : List Symbol :=
  match decode word with
  | none => []
  | some (M, d, f) =>
      if d = 0 then if label = [] then word else []
      else match labelValue label with
        | none => []
        | some b => (f.substitute d b).encode M (d - 1)

theorem wordReduce_encode_bit {M d : ℕ} (bound : d + 1 ≤ M) (f : Formula)
    (valid : f.valid (d + 1)) (b : Bool) :
    wordReduce (f.encode M (d + 1)) [bitSymbol b] =
      (f.substitute (d + 1) b).encode M d := by
  simp [wordReduce, decode_encode bound f valid]

theorem word_reduce_length (word label : List Symbol) :
    (wordReduce word label).length ≤ word.length := by
  cases decoded : decode word with
  | none => simp [wordReduce, decoded]
  | some result =>
    rcases result with ⟨M, d, f⟩
    obtain ⟨bound, valid, equal⟩ := decode_sound word M d f decoded
    cases d with
    | zero => by_cases empty : label = [] <;> simp [wordReduce, decoded, empty]
    | succ d =>
      cases bit : labelValue label with
      | none => simp [wordReduce, decoded, bit]
      | some b =>
        have length := f.substitute_encoding_length bound b valid
        simp only [wordReduce, decoded, Nat.add_one_ne_zero, ite_false, bit,
          Nat.add_sub_cancel]
        rw [length, equal]

theorem word_reduce_rank (word label : List Symbol) :
    wordRank (wordReduce word label) ≤ wordRank word - wordWidth word := by
  cases decoded : decode word with
  | none => simp [wordReduce, decoded]
  | some result =>
    rcases result with ⟨M, d, f⟩
    obtain ⟨bound, valid, equal⟩ := decode_sound word M d f decoded
    have originalRank : wordRank word = d := by rw [← equal, wordRank_encode bound f valid]
    cases d with
    | zero =>
      by_cases empty : label = [] <;>
        simp [wordReduce, decoded, empty, originalRank, wordWidth, width]
    | succ d =>
      cases bit : labelValue label with
      | none => simp [wordReduce, decoded, bit]
      | some b =>
        have rank := wordRank_encode (by omega : d ≤ M) (f.substitute (d + 1) b)
          (f.valid_substitute b valid)
        simpa [wordReduce, decoded, bit, originalRank, wordWidth, width] using rank.le

end ComplexityOfGenerators.Examples.PaddedCNF
