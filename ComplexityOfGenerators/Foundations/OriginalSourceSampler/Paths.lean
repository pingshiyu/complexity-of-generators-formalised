import ComplexityOfGenerators.Foundations.ExecutionRegions
import ComplexityOfGenerators.Foundations.StreamSemanticsProperties

/-! Exact random consumption of native source calls. A minimal accepting
seed contains exactly the bits read by the terminal native path. Ordinary
instructions consume no random bits, including arbitrarily long phases. -/
namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O)

theorem next_randomHead_mono {data : InputData I A} {bits : BitString}
    {current following : Configuration M}
    (step : M.next data bits current = .running following) :
    current.randomHead ≤ following.randomHead := by
  unfold next at step
  split at step
  · cases step
  · cases step
  · split at step
    · cases step
    · cases step; simp
  · cases step; exact le_rfl

theorem Steps.randomHead_mono {data : InputData I A} {bits : BitString}
    {start finish : Configuration M} {time : ℕ}
    (path : M.Steps data bits start time finish) : start.randomHead ≤ finish.randomHead := by
  induction path with
  | refl => exact le_rfl
  | tail path step ih => exact ih.trans (M.next_randomHead_mono step)

theorem next_randomHead_le_succ {data : InputData I A} {bits : BitString}
    {current following : Configuration M}
    (step : M.next data bits current = .running following) :
    following.randomHead ≤ current.randomHead+1 := by
  unfold next at step
  split at step
  · cases step
  · cases step
  · split at step
    · cases step
    · cases step; exact le_rfl
  · cases step; exact Nat.le_succ _

theorem Steps.randomHead_le_time {data : InputData I A} {bits : BitString}
    {start finish : Configuration M} {time : ℕ}
    (path : M.Steps data bits start time finish) :
    finish.randomHead ≤ start.randomHead+time := by
  induction path with
  | refl => simp
  | tail path step ih =>
      have next := M.next_randomHead_le_succ step
      omega

theorem next_randomHead_le_length {data : InputData I A} {bits : BitString}
    {current following : Configuration M}
    (step : M.next data bits current = .running following)
    (bound : current.randomHead ≤ bits.length) : following.randomHead ≤ bits.length := by
  unfold next at step
  split at step
  · cases step
  · cases step
  · split at step
    · cases step
    · rename_i bit lookup
      have available := (List.getElem?_eq_some_iff.mp lookup).1
      cases step
      simp only
      omega
  · cases step; exact bound

theorem Steps.randomHead_le_length {data : InputData I A} {bits : BitString}
    {start finish : Configuration M} {time : ℕ}
    (path : M.Steps data bits start time finish) (bound : start.randomHead ≤ bits.length) :
    finish.randomHead ≤ bits.length := by
  induction path with
  | refl => exact bound
  | tail path step ih => exact M.next_randomHead_le_length step ih

theorem next_eq_of_consumed_agreement {data : InputData I A} {first second : BitString}
    {current following : Configuration M}
    (step : M.next data first current = .running following)
    (agreement : ∀ j < following.randomHead, first[j]? = second[j]?) :
    M.next data second current = .running following := by
  unfold next at step ⊢
  split at step <;> rename_i action
  · cases step
  · cases step
  · split at step
    · cases step
    · rename_i bit lookup
      cases step
      rw [← agreement current.randomHead (by simp), lookup]
  · simpa only [action] using step

/-- Replay the same actual path using precisely its consumed random prefix.
No equality of unused random cells is required. -/
theorem Steps.change_consumed_bits {data : InputData I A} {first second : BitString}
    {start finish : Configuration M} {time : ℕ}
    (path : M.Steps data first start time finish)
    (agreement : ∀ j < finish.randomHead, first[j]? = second[j]?) :
    M.Steps data second start time finish := by
  induction path with
  | refl => exact .refl
  | @tail time current following path step ih =>
      apply (ih fun j bound => agreement j (bound.trans_le (M.next_randomHead_mono step))).tail
      exact M.next_eq_of_consumed_agreement step agreement

theorem observe_accepted_independent_bits {data : InputData I A} {first second : BitString}
    {current : Configuration M} {word : List O}
    (accepted : M.observe data first current = .halted (.accepted word)) :
    M.observe data second current = .halted (.accepted word) := by
  unfold observe at accepted ⊢
  split at accepted <;> rename_i action
  · simpa only [action] using accepted
  · cases accepted
  · split_ifs at accepted; cases accepted
  · cases accepted

/-- The terminal cursor of every accepting path on a minimal seed is exactly
the seed length. This includes acceptance without randomness. -/
theorem MinimalAcceptedSeed.randomHead_eq {data : InputData I A} {bits : BitString}
    (minimal : M.MinimalAcceptedSeed data bits) {time : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration time finish) {word : List O}
    (accepted : M.observe data bits finish = .halted (.accepted word)) :
    finish.randomHead = bits.length := by
  have bound := path.randomHead_le_length M (by simp [initialConfiguration])
  apply le_antisymm bound
  by_contra shorter
  have replay : M.Steps data (bits.take finish.randomHead) M.initialConfiguration time finish :=
    path.change_consumed_bits M (fun j before => by simp [before])
  have terminal := M.observe_accepted_independent_bits (second := bits.take finish.randomHead) accepted
  have run := replay.runFrom M
  rw [runFrom_initial, terminal] at run
  exact minimal.2 finish.randomHead (by omega) ⟨word, time, run⟩

end ComplexityOfGenerators.Machine
