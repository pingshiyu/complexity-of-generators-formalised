import ComplexityOfGenerators.ComplexityClasses
import Mathlib.Data.Set.Finite.Basic

/-! Elementary facts about exact-length language slices. -/

namespace ComplexityOfGenerators

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
