import ComplexityOfGenerators.Simulation.ExactRecursive.SearchView

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

namespace SearchStored

variable {B V} {n : ℕ} {y label : List α} {bits : BitString}
    {selection : BoundedTrialChoice.Selection (List α)} {s : Store B V}

theorem replace_random (h : SearchStored B V n y label bits selection s) (rest : BitString) :
    SearchStored B V n y label rest selection (Function.update s 17 (rest.map Symbol.bit)) := by
  rcases h with ⟨hi, hl, hn, hr, he, hc, hk, hf⟩
  constructor <;> simp_all [SelectionStored]

theorem after_offer (h : SearchStored B V n y label bits selection s) (coin : Bool)
    (status : Source.Status (Fin V.states)) (output : List α)
    (state : s 0 = [.inverse (.state status)])
    (result : s 10 = output.map (fun a => Symbol.inverse (Source.Cell.output a))) :
    SearchStored B V n y label bits (selection.offer (positiveResult V label status output) coin)
      ((offer B V coin).eval s) := by
  have fixed (j : Fin 35) (h10 : j ≠ 10) (h25 : j ≠ 25) (h26 : j ≠ 26) (h27 : j ≠ 27) :=
    offer_fixes B V coin j h10 h25 h26 h27 s
  refine ⟨(fixed 11 (by decide) (by decide) (by decide) (by decide)).trans h.input,
    (fixed 12 (by decide) (by decide) (by decide) (by decide)).trans h.label, ?_,
    (fixed 17 (by decide) (by decide) (by decide) (by decide)).trans h.random,
    (fixed 14 (by decide) (by decide) (by decide) (by decide)).trans h.empty,
    offer_stored B V coin s selection label output status h.selection h.label state result⟩
  exact (congrArg List.length (fixed 13 (by decide) (by decide) (by decide) (by decide))).trans h.index

theorem after_increment (h : SearchStored B V n y label bits selection s) (first : α) :
    SearchStored B V n y (Shortlex.next first label) bits selection ((increment B V first).eval s) := by
  have fixed (j : Fin 35) (h12 : j ≠ 12) (h24 : j ≠ 24) := increment_fixes B V first j h12 h24 s
  refine ⟨(fixed 11 (by decide) (by decide)).trans h.input, increment_word B V first s label h.label, ?_,
    (fixed 17 (by decide) (by decide)).trans h.random, (fixed 14 (by decide) (by decide)).trans h.empty,
    increment_selection B V first s selection h.selection⟩
  exact (congrArg List.length (fixed 13 (by decide) (by decide))).trans h.index

end SearchStored

/-- A complete native scan iteration implements one isolated inverse trial,
one offer coin, and one increment of the label counter. -/
theorem searchStep_correct (first : α) (seed time : PolynomialBound) (n : ℕ)
    (y label : List α) (bits : BitString) (selection : BoundedTrialChoice.Selection (List α)) (s : Store B V)
    (stored : SearchStored B V n y label bits selection s) (enough : seed n + 1 ≤ bits.length) :
    SearchStored B V n y (Shortlex.next first label) (bits.drop (seed n + 1))
      (selection.offer (positiveValue V time n y label (bits.take (seed n))) (bits[seed n]? == some true))
      ((searchStep B V first seed time).eval s) := by
  obtain ⟨status, output, trial, state, result, value⟩ := inverseTrial_view B V seed time n y label bits selection s stored
  cases drop_eq : bits.drop (seed n) with
  | nil => have length := congrArg List.length drop_eq; simp only [List.length_drop, List.length_nil] at length; omega
  | cons bit rest =>
    have bit_eq : bits[seed n]? = some bit := by
      rw [← List.head?_drop, drop_eq]
      rfl
    have rest_eq : bits.drop (seed n + 1) = rest := by
      simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail drop_eq
    have popView := trial.replace_random rest
    have selected := popView.after_offer bit status output
      (by simpa using state) (by simpa using result)
    rw [value] at selected
    have incremented := selected.after_increment first
    have read := coin_eval B V (offer B V false) (offer B V true) ((inverseTrial B V seed time).eval s)
      bit rest (by simpa only [drop_eq] using trial.random)
    simp only [searchStep, WordStack.Routine.seq, read, rest_eq, bit_eq]
    cases bit <;> simpa using incremented

end ComplexityOfGenerators.Simulation.ExactRecursive
