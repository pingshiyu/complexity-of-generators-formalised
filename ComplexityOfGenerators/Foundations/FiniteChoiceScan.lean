import ComplexityOfGenerators.Machine

/-! Fixed-consumption finite scans share seed-trace proofs independently of
native controller implementations. A retained answer can be preserved, and
one selected item can force any of its supported answers. -/

namespace ComplexityOfGenerators.FiniteChoiceScan

variable {I A : Type}

abbrev State (A : Type) := Option A × BitString

def cost (size : I → ℕ) (items : List I) : ℕ := (items.map size).sum

def TraceSpec (step : I → State A → State A) (size : I → ℕ) : Prop :=
  ∀ i previous, ∃ block : BitString, ∃ answer : Option A,
    block.length = size i ∧
    (∀ word, previous = some word → answer = some word) ∧
    ∀ tail, step i (previous, block ++ tail) = (answer, tail)

variable (step : I → State A → State A) (size : I → ℕ) (traces : TraceSpec step size)

include traces in
theorem fold_trace (items : List I) (previous : Option A) :
    ∃ block : BitString, ∃ answer : Option A,
      block.length = cost size items ∧
      (∀ word, previous = some word → answer = some word) ∧
      ∀ tail, items.foldl (fun p i => step i p) (previous, block ++ tail) = (answer, tail) := by
  induction items generalizing previous with
  | nil => exact ⟨[], previous, rfl, fun _ equal => equal, by simp⟩
  | cons i rest ih =>
    obtain ⟨first, chosen, firstLength, preserved, firstRun⟩ := traces i previous
    obtain ⟨block, answer, length, preserve, trace⟩ := ih chosen
    refine ⟨first ++ block, answer, ?_, ?_, ?_⟩
    · simp [cost, List.length_append, firstLength, length]
    · exact fun word equal => preserve word (preserved word equal)
    · intro tail
      rw [List.foldl_cons, List.append_assoc, firstRun, trace]

include traces in
theorem fold_keep (items : List I) (word : A) :
    ∃ block : BitString, block.length = cost size items ∧
      ∀ tail, items.foldl (fun p i => step i p) (some word, block ++ tail) = (some word, tail) := by
  obtain ⟨block, answer, length, preserve, trace⟩ := fold_trace step size traces items (some word)
  have equal := preserve word rfl
  exact ⟨block, length, by simpa only [equal] using trace⟩

include traces in
theorem fold_choose (items : List I) (i : I) (occurs : i ∈ items) (word : A)
    (forcing : ∃ block : BitString, block.length = size i ∧
      ∀ previous tail, step i (previous, block ++ tail) = (some word, tail)) :
    ∃ block : BitString, block.length = cost size items ∧
      ∀ tail, items.foldl (fun p i => step i p) (none, block ++ tail) = (some word, tail) := by
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp occurs
  subst items
  obtain ⟨prefixBits, previous, prefixLength, _, prefixRun⟩ := fold_trace step size traces before none
  obtain ⟨chosen, chosenLength, chosenRun⟩ := forcing
  obtain ⟨suffix, suffixLength, suffixRun⟩ := fold_keep step size traces after word
  refine ⟨prefixBits ++ chosen ++ suffix, ?_, ?_⟩
  · simp [List.length_append, prefixLength, chosenLength, suffixLength, cost, List.sum_append]
  · intro tail
    simp only [List.foldl_append, List.foldl_cons]
    have prefixRun' := prefixRun (chosen ++ suffix ++ tail)
    have chosenRun' := chosenRun previous (suffix ++ tail)
    simp only [List.append_assoc] at prefixRun' chosenRun' ⊢
    rw [prefixRun', chosenRun', suffixRun]

end ComplexityOfGenerators.FiniteChoiceScan
