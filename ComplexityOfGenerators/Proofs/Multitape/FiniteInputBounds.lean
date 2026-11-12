import ComplexityOfGenerators.MultitapeComplexityClasses
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold

/-! A finite set of bounded-length inputs has a finite common all-branch time
bound. This bound is used only in termination/productivity proofs for the
space converse: it is not computed, loaded, or queried by any machine. -/

namespace ComplexityOfGenerators.MultitapeMachine

variable {I A O : Type} {M : MultitapeMachine I A O}

theorem TimeBound.mono {data : InputData I A} {small large : ℕ}
    (bounded : M.TimeBound data small) (budget : small ≤ large) : M.TimeBound data large := by
  intro bits
  obtain ⟨ticks, result, cost, execution⟩ := bounded bits
  exact ⟨ticks, result, cost.trans budget, execution⟩

end ComplexityOfGenerators.MultitapeMachine

namespace ComplexityOfGenerators.Multitape

variable {α O : Type} [Fintype α]

theorem filterMap_ofFn_lookup (word : Word α) (n : ℕ) (small : word.length ≤ n) :
    (List.ofFn (fun i : Fin n => word[i.val]?)).filterMap id = word := by
  induction n generalizing word with
  | zero =>
      have empty : word = [] := List.length_eq_zero_iff.mp (by omega)
      subst word
      simp
  | succ n ih =>
      cases word with
      | nil => simp
      | cons value tail =>
        rw [List.ofFn_succ]
        simp only [Fin.val_zero, List.getElem?_cons_zero, List.filterMap_cons,
          id_eq, Fin.val_succ, List.getElem?_cons_succ]
        exact congrArg (List.cons value) (ih tail (by simpa using small))

/-- No computability claim is made about the maximum: the same concrete source
machine runs directly and already halts on every individual input. -/
theorem finite_input_timeBound (M : MultitapeMachine α Bool O)
    (termination : ∀ word, ∃ time, M.TimeBound (decisionData word) time) (n : ℕ) :
    ∃ time, ∀ word, word.length ≤ n → M.TimeBound (decisionData word) time := by
  classical
  let chosen (word : Word α) : ℕ := Classical.choose (termination word)
  have chosenBound (word : Word α) : M.TimeBound (decisionData word) (chosen word) :=
    Classical.choose_spec (termination word)
  let decode (values : Fin n → Option α) : Word α := (List.ofFn values).filterMap id
  let budget := (Finset.univ : Finset (Fin n → Option α)).sup (fun values => chosen (decode values))
  refine ⟨budget, ?_⟩
  intro word small
  let values : Fin n → Option α := fun i => word[i.val]?
  have decoded : decode values = word := filterMap_ofFn_lookup word n small
  have bound : chosen word ≤ budget := by
    have before : chosen (decode values) ≤ budget :=
      Finset.le_sup (f := fun values => chosen (decode values)) (Finset.mem_univ values)
    simpa only [decoded] using before
  exact (chosenBound word).mono bound

end ComplexityOfGenerators.Multitape
