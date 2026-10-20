import ComplexityOfGenerators.Simulation.ExactRecursive.SearchStep

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def entriesFrom (first : α) (time : PolynomialBound) (n : ℕ) (y : List α) :
    ℕ → List α → List (BitString → Option (List α))
  | 0, _ => []
  | count + 1, label => positiveValue V time n y label ::
      entriesFrom first time n y count (Shortlex.next first label)

theorem entriesFrom_eq (first : α) (time : PolynomialBound) (n : ℕ) (y : List α) (count : ℕ) (label : List α) :
    entriesFrom V first time n y count label =
      (List.range count).map (fun i => positiveValue V time n y ((Shortlex.next first)^[i] label)) := by
  induction count generalizing label with
  | zero => rfl
  | succ count ih =>
    simp [entriesFrom, ih, List.range_succ_eq_map, List.map_map, Function.comp_def, Function.iterate_succ_apply]

/-- Induction over the implemented clocked loop, including the discarded
random blocks after a selection has been locked. -/
theorem searchIter_correct (first : α) (seed time : PolynomialBound) (n count : ℕ)
    (y label : List α) (bits : BitString) (selection : BoundedTrialChoice.Selection (List α)) (s : Store B V)
    (stored : SearchStored B V n y label bits selection s)
    (enough : count * (seed n + 1) ≤ bits.length) :
    SearchStored B V n y ((Shortlex.next first)^[count] label) (bits.drop (count * (seed n + 1)))
      (BoundedTrialChoice.scan (seed n) (entriesFrom V first time n y count label) bits selection)
      ((WordStack.Routine.counted 23 (searchStep B V first seed time)).eval^[count] s) := by
  induction count generalizing label bits selection s with
  | zero => simpa only [Function.iterate_zero, id_eq, Nat.zero_mul, List.drop_zero, entriesFrom,
      BoundedTrialChoice.scan] using stored
  | succ count ih =>
    have firstEnough : seed n + 1 ≤ bits.length := by
      have positive := Nat.le_mul_of_pos_left (seed n + 1) (by omega : 0 < count + 1)
      omega
    have firstRun := searchStep_correct B V first seed time n y label bits selection
      ((Local.pop (23 : Fin 35)).eval s) stored.counter_pop firstEnough
    have remaining : count * (seed n + 1) ≤ (bits.drop (seed n + 1)).length := by
      simp only [List.length_drop]
      simp only [Nat.add_mul, Nat.one_mul] at enough
      omega
    have rest := ih (Shortlex.next first label) (bits.drop (seed n + 1))
      (selection.offer (positiveValue V time n y label (bits.take (seed n))) (bits[seed n]? == some true))
      _ firstRun remaining
    have dropping : (bits.drop (seed n + 1)).drop (count * (seed n + 1)) =
        bits.drop ((count + 1) * (seed n + 1)) := by
      rw [List.drop_drop]
      congr 1
      ring
    simpa only [Function.iterate_succ_apply, entriesFrom, BoundedTrialChoice.scan,
      WordStack.Routine.counted, WordStack.Routine.seq, WordStack.Routine.ofLocal, dropping] using rest

theorem searchSetup_view (count : PolynomialBound) (n : ℕ) (y : List α) (bits : BitString) (s : Store B V)
    (input : s 11 = letters B V y) (index : (s 13).length = n) (random : s 17 = bits.map Symbol.bit)
    (empty : s 14 = []) :
    SearchStored B V n y [] bits ⟨none, false⟩ ((searchSetup B V count).eval s) := by
  constructor <;>
    simp [searchSetup, WordStack.Routine.seq, WordStack.Routine.clear, flag_eval,
      counter, CounterRoutine.routine_eval, input, index, random, empty,
      SelectionStored, letters, held, flagWord]

theorem searchSetup_count (count : PolynomialBound) (n : ℕ) (s : Store B V) (index : (s 13).length = n) :
    (((searchSetup B V count).eval s) 23).length = count n := by
  simp [searchSetup, WordStack.Routine.seq, WordStack.Routine.clear, flag_eval,
    counter, CounterRoutine.routine_eval, index]

end ComplexityOfGenerators.Simulation.ExactRecursive
