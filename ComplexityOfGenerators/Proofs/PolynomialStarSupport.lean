import ComplexityOfGenerators.Simulation.StarGenerator.Value
import ComplexityOfGenerators.Proofs.PolynomialConcatenationSupport
import ComplexityOfGenerators.Foundations.StarSupport

namespace ComplexityOfGenerators.Simulation.StarGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

def Correct (P : ℕ → List α → Prop) (table : Table α) : Prop :=
  ∀ i word, (table[i]?.bind id) = some word → P i word

def Sized (table : Table α) : Prop := Correct (fun i word => word.length = i) table

def SourceSized (G : Machine Unit Bool α) (time : PolynomialBound) : Prop :=
  ∀ j bits word, UnionGenerator.sourceValue G time j bits = some word → word.length = j

/-- An invariant of concatenating a generated first factor with an old entry. -/
def Combines (G : Machine Unit Bool α) (time : PolynomialBound)
    (P : ℕ → List α → Prop) : Prop :=
  ∀ m j bits u v, 1 ≤ j → j ≤ m →
    UnionGenerator.sourceValue G time j bits = some u → P (m - j) v → P m (u ++ v)

variable (G : Machine Unit Bool α) (seed time : PolynomialBound)

include G seed time in
theorem next_correct (P : ℕ → List α → Prop) (combine : Combines G time P)
    (table : Table α) (correct : Correct P table) (m j : ℕ) (positive : 1 ≤ j) (index : j ≤ m)
    (p : Option (List α) × BitString) (previous : ∀ word, p.1 = some word → P m word) :
    ∀ word, (next G seed time table m j p).1 = some word → P m word := by
  intro word output
  rcases ConcatenationGenerator.offer_some _ output with old | candidate
  · exact previous word old
  · obtain ⟨u, v, source, entry, rfl⟩ := ConcatenationGenerator.pairValue_some candidate
    exact combine m j _ u v positive index source (correct (m - j) v entry)

theorem stage_correct (P : ℕ → List α → Prop) (combine : Combines G time P)
    (table : Table α) (correct : Correct P table) (m : ℕ) (bits : BitString) :
    ∀ word, (stage G seed time table m bits).1 = some word → P m word := by
  have fold (splits : List ℕ) (indices : ∀ j ∈ splits, 1 ≤ j ∧ j ≤ m)
      (p : Option (List α) × BitString) (valid : ∀ word, p.1 = some word → P m word) :
      ∀ word, (splits.foldl (fun p j => next G seed time table m j p) p).1 = some word → P m word := by
    induction splits generalizing p with
    | nil => exact valid
    | cons j rest ih =>
      exact ih (by intro k hk; exact indices k (by simp [hk])) _
        (next_correct G seed time P combine table correct m j (indices j (by simp)).1 (indices j (by simp)).2 p valid)
  apply fold (List.range' 1 m) _ (none, bits) (by intro word impossible; cases impossible)
  intro j member
  obtain ⟨k, bound, rfl⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul]
  omega

theorem correct_append (P : ℕ → List α → Prop) (table : Table α) (correct : Correct P table)
    (m : ℕ) (length : table.length = m) (answer : Option (List α))
    (valid : ∀ word, answer = some word → P m word) : Correct P (table ++ [answer]) := by
  intro i word output
  by_cases old : i < table.length
  · rw [List.getElem?_append_left old] at output
    exact correct i word output
  · rw [List.getElem?_append_right (by omega)] at output
    by_cases equal : i = m
    · subst i
      rw [length, Nat.sub_self] at output
      exact valid word output
    · have large : 1 ≤ i - table.length := by omega
      have absent : ([answer] : Table α)[i - table.length]? = none :=
        List.getElem?_eq_none (by simpa using large)
      rw [absent] at output
      cases output

theorem extend_correct (P : ℕ → List α → Prop) (combine : Combines G time P)
    (m : ℕ) (p : Table α × BitString) (correct : Correct P p.1) (length : p.1.length = m) :
    Correct P (extend G seed time m p).1 :=
  correct_append P p.1 correct m length _ (stage_correct G seed time P combine p.1 correct m p.2)

@[simp] theorem extend_length (m : ℕ) (p : Table α × BitString) :
    (extend G seed time m p).1.length = p.1.length + 1 := by simp [extend]

theorem tableRun_succ (n : ℕ) (bits : BitString) :
    tableRun G seed time (n + 1) bits = extend G seed time (n + 1) (tableRun G seed time n bits) := by
  simp [tableRun, List.range'_concat, List.foldl_append, Nat.add_comm]

@[simp] theorem tableRun_length (n : ℕ) (bits : BitString) :
    (tableRun G seed time n bits).1.length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tableRun_succ, extend_length, ih]

theorem correct_initial (P : ℕ → List α → Prop) (empty : P 0 []) : Correct P [some []] := by
  intro i word output
  cases i with
  | zero => have equal : [] = word := Option.some.inj output; simpa [← equal] using empty
  | succ i => simp at output

theorem tableRun_correct (P : ℕ → List α → Prop) (empty : P 0 []) (combine : Combines G time P)
    (n : ℕ) (bits : BitString) : Correct P (tableRun G seed time n bits).1 := by
  induction n with
  | zero => exact correct_initial P empty
  | succ n ih =>
    rw [tableRun_succ]
    exact extend_correct G seed time P combine (n + 1) (tableRun G seed time n bits) ih (tableRun_length G seed time n bits)

theorem algorithm_correct (P : ℕ → List α → Prop) (empty : P 0 []) (combine : Combines G time P)
    (n : ℕ) (bits : BitString) (word : List α)
    (output : algorithm G seed time n bits = some word) : P n word := by
  have correct := tableRun_correct G seed time P empty combine n bits
  apply correct n word
  simpa only [algorithm, List.getLast?_eq_getElem?, tableRun_length, Nat.add_sub_cancel] using output

/-- The exact-length source condition is a theorem about the actual source
machine, and is discharged for GeneratorFamily rather than assumed as a compiler. -/
theorem generator_sourceSized (F : GeneratorFamily α) : SourceSized F.machine time := by
  intro j bits word output
  exact F.outputLength j word (UnionGenerator.sourceValue_mem F.toUniformGenerators time j bits word output)

theorem sized_combines (sized : SourceSized G time) : Combines G time (fun i word => word.length = i) := by
  intro m j bits u v _ index source previous
  simp only [List.length_append, sized j bits u source, previous]
  omega

theorem stage_sized (sized : SourceSized G time) (table : Table α) (correct : Sized table)
    (m : ℕ) (bits : BitString) :
    ∀ word, (stage G seed time table m bits).1 = some word → word.length = m :=
  stage_correct G seed time _ (sized_combines G time sized) table correct m bits

theorem tableRun_sized (sized : SourceSized G time) (n : ℕ) (bits : BitString) :
    Sized (tableRun G seed time n bits).1 :=
  tableRun_correct G seed time _ rfl (sized_combines G time sized) n bits

theorem star_combines (F : GeneratorFamily α) :
    Combines F.machine time (fun i word => word ∈ lengthSlice (IndexedSupport.star F.toUniformGenerators.language) i) := by
  intro m j bits u v positive index source previous
  have member := UnionGenerator.sourceValue_mem F.toUniformGenerators time j bits u source
  exact IndexedSupport.star_slice_compose _ (by omega) index
    ⟨⟨j, member⟩, F.outputLength j u member⟩ previous

theorem algorithm_sound (F : GeneratorFamily α) (n : ℕ) (bits : BitString) (word : List α)
    (output : algorithm F.machine seed time n bits = some word) :
    word ∈ lengthSlice (IndexedSupport.star F.toUniformGenerators.language) n :=
  algorithm_correct F.machine seed time _ ⟨IndexedSupport.nil_mem_star _, rfl⟩ (star_combines time F) n bits word output


/-- Uniform storage bound at a fixed outer target, valid for any source machine
because each source call is clocked. -/
def BoundedAt (n bound : ℕ) (table : Table α) : Prop :=
  Correct (fun i word => i ≤ n → word.length ≤ i * bound) table

theorem clocked_source_length (j : ℕ) (bits : BitString) (word : List α)
    (output : UnionGenerator.sourceValue G time j bits = some word) : word.length ≤ time j :=
  G.accepted_output_length_le (generatorData j) bits (time j) word
    ((UnionGenerator.sourceValue_eq_some_iff G time j bits word).mp output)

theorem clocked_combines (n : ℕ) :
    Combines G time (fun i word => i ≤ n → word.length ≤ i * time n) := by
  intro m j bits u v positive index source previous target
  have length := clocked_source_length G time j bits u source
  have timeBound := time.monotone (by omega : j ≤ n)
  have suffix := previous (by omega : m - j ≤ n)
  have factor : time n ≤ j * time n := by nlinarith
  simp only [List.length_append]
  have sum : j + (m - j) = m := by omega
  nlinarith

theorem stage_bounded (n : ℕ) (table : Table α) (bounded : BoundedAt n (time n) table)
    (m : ℕ) (target : m ≤ n) (bits : BitString) :
    ∀ word, (stage G seed time table m bits).1 = some word → word.length ≤ m * time n := by
  intro word output
  exact stage_correct G seed time _ (clocked_combines G time n) table bounded m bits word output target

theorem extend_bounded (n m : ℕ) (p : Table α × BitString) (bounded : BoundedAt n (time n) p.1)
    (length : p.1.length = m) : BoundedAt n (time n) (extend G seed time m p).1 :=
  extend_correct G seed time _ (clocked_combines G time n) m p bounded length

theorem tableRun_bounded (n steps : ℕ) (bits : BitString) :
    BoundedAt n (time n) (tableRun G seed time steps bits).1 :=
  tableRun_correct G seed time _ (by simp) (clocked_combines G time n) steps bits

end
end ComplexityOfGenerators.Simulation.StarGenerator
