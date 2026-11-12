import ComplexityOfGenerators.Foundations.IndexedSupportClosure

namespace ComplexityOfGenerators.IndexedSupport
variable {α : Type}

/-- Empty source words do not affect a finite concatenation. -/
theorem flatten_mem_star {L : Language α} (words : List (List α))
    (members : ∀ word ∈ words, word ∈ L) : words.flatten ∈ star L := by
  induction words with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons word rest ih =>
    obtain ⟨witness,valid,equal⟩ := ih (fun u member => members u (by simp [member]))
    by_cases empty : word = []
    · simpa only [empty,List.flatten_cons,List.nil_append] using (show rest.flatten ∈ star L from ⟨witness,valid,equal⟩)
    · refine ⟨word::witness,?_,?_⟩
      · intro u member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨members u (by simp),empty⟩
        · exact valid u member
      · simpa only [List.flatten_cons,equal]

theorem mem_star_of_mem {L : Language α} {word : List α} (member : word ∈ L) : word ∈ star L := by
  simpa using flatten_mem_star [word] (by simpa using member)

theorem star_infinite {L : Language α} (infinite : L.Infinite) : (star L).Infinite :=
  infinite.mono (fun _ member => mem_star_of_mem member)

private theorem choose_positive_indices (G : Layers α) (zero : ∀ word ∈ G 0, word = [])
    (words : List (List α)) (members : ∀ word ∈ words, word ∈ language G ∧ word ≠ []) :
    ∃ indices, List.Forall₂ (fun i word => 0 < i ∧ word ∈ G i) indices words := by
  induction words with
  | nil => exact ⟨[],.nil⟩
  | cons word rest ih =>
    have head := members word (by simp)
    obtain ⟨index,generated⟩ := head.1
    have positive : 0 < index := by
      by_contra missing
      have equal : index = 0 := by omega
      subst index
      exact head.2 (zero word generated)
    obtain ⟨indices,tail⟩ := ih (fun u member => members u (by simp [member]))
    exact ⟨index::indices,.cons ⟨positive,generated⟩ tail⟩

/-- Positive-index concatenations give exactly Kleene star when the source's
zero-index words are empty. No producing-index bound is needed here. -/
theorem star_language (G : Layers α) (zero : ∀ word ∈ G 0, word = []) :
    language (starLayers G) = star (language G) := by
  ext word
  constructor
  · rintro ⟨n,indices,words,generated,total,rfl⟩
    clear total n
    apply flatten_mem_star words
    have members : ∀ u ∈ words, u ∈ language G := by
      induction generated with
      | nil => simp
      | @cons i u indices words first rest ih =>
        intro v member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨i,first.2⟩
        · exact ih v member
    exact members
  · rintro ⟨words,members,rfl⟩
    obtain ⟨indices,generated⟩ := choose_positive_indices G zero words members
    exact ⟨indices.sum,indices,words,generated,rfl,rfl⟩

/-- Exact source members make every concatenation member exact as well. -/
theorem starLayers_length (G : Layers α) (exactLength : ∀ i word, word ∈ G i → word.length = i)
    (n : ℕ) (word : List α) (member : word ∈ starLayers G n) : word.length = n := by
  obtain ⟨indices,words,generated,total,rfl⟩ := member
  have lengths : words.flatten.length = indices.sum := by
    clear total n
    induction generated with
    | nil => rfl
    | @cons i u indices words first rest ih =>
      simpa only [List.flatten_cons,List.length_append,List.sum_cons,exactLength i u first.2,ih]
  exact lengths.trans total

/-- Every accepted indexed concatenation supplies a positive composition
of nonempty source members. -/
theorem starLayers_available (G : Layers α) (n : ℕ) (word : List α) (member : word ∈ starLayers G n) :
    ∃ indices : List ℕ, indices.sum = n ∧ ∀ j ∈ indices, 0 < j ∧ (G j).Nonempty := by
  obtain ⟨indices,words,generated,total,rfl⟩ := member
  refine ⟨indices,total,?_⟩
  clear total n
  induction generated with
  | nil => simp
  | @cons j word indices words first rest ih =>
    intro k belongs
    rcases List.mem_cons.mp belongs with rfl | belongs
    · exact ⟨first.1,word,first.2⟩
    · exact ih k belongs

end ComplexityOfGenerators.IndexedSupport
