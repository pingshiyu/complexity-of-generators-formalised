import ComplexityOfGenerators.ComplexityClasses
import Mathlib.Data.Set.Finite.Basic

/-! Elementary facts about exact-length language slices. -/

namespace ComplexityOfGenerators

/-- Over a finite alphabet there are finitely many words of any exact length. -/
theorem finite_words_length_eq (α : Type) [Fintype α] (n : ℕ) :
    {word : List α | word.length = n}.Finite := by
  classical
  apply (Set.finite_range (fun letters : Fin n → α => List.ofFn letters)).subset
  intro word length
  subst n
  exact ⟨fun i : Fin word.length => word[i.val], List.ofFn_getElem⟩

/-- The words below a fixed length bound form a finite set. -/
theorem finite_words_length_le (α : Type) [Fintype α] (n : ℕ) :
    {word : List α | word.length ≤ n}.Finite := by
  apply ((Finset.range (n + 1)).finite_toSet.biUnion (fun k _ => finite_words_length_eq α k)).subset
  intro word length
  exact Set.mem_iUnion.mpr ⟨word.length, Set.mem_iUnion.mpr ⟨by simpa using length, rfl⟩⟩

/-- A language with an instance at every requested length is infinite. -/
theorem language_infinite_of_nonempty_slices {α : Type} (L : Language α)
    (nonempty : ∀ n, (lengthSlice L n).Nonempty) : L.Infinite := by
  classical
  let word : ℕ → List α := fun n => (nonempty n).choose
  have property (n : ℕ) : word n ∈ L ∧ (word n).length = n :=
    (nonempty n).choose_spec
  apply Set.infinite_of_injective_forall_mem (f := word)
  · intro n m equal
    have lengths := congrArg List.length equal
    simpa only [(property n).2, (property m).2] using lengths
  · exact fun n => (property n).1

end ComplexityOfGenerators
