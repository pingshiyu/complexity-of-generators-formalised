import ComplexityOfGenerators.Simulation.ExactRecursive.Selection
import ComplexityOfGenerators.Simulation.ExactRecursive.Trial

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def inverseValue (time : PolynomialBound) (n : ℕ) (y label : List α) (bits : BitString) : Option (List α) :=
  match V.run {input := y, auxiliary := label, index := n} bits (time n) with
  | .halted (.accepted word) => some word
  | _ => none

theorem inverseValue_eq_some (time : PolynomialBound) (n : ℕ) (y label : List α) (bits : BitString) (word : List α) :
    inverseValue V time n y label bits = some word ↔
      V.run {input := y, auxiliary := label, index := n} bits (time n) = .halted (.accepted word) := by
  unfold inverseValue
  cases V.run {input := y, auxiliary := label, index := n} bits (time n) with
  | running c => simp
  | halted outcome => cases outcome <;> simp

def positiveValue (time : PolynomialBound) (n : ℕ) (y label : List α) (bits : BitString) : Option (List α) :=
  if label = [] then none else inverseValue V time n y label bits

theorem positiveResult_eq (time : PolynomialBound) (n : ℕ) (y label output : List α) (bits : BitString)
    (status : Source.Status (Fin V.states))
    (rep : ∀ word, (status = .accepted ∧ output.reverse = word) ↔
      V.run {input := y, auxiliary := label, index := n} bits (time n) = .halted (.accepted word)) :
    positiveResult V label status output = positiveValue V time n y label bits := by
  by_cases empty : label = []
  · simp [positiveResult, positiveValue, empty]
  · apply Option.ext
    intro word
    rw [positiveValue, ite_eq_right empty, inverseValue_eq_some, ← rep]
    cases status <;> simp [positiveResult, empty]

structure SearchStored (n : ℕ) (y label : List α) (bits : BitString)
    (selection : BoundedTrialChoice.Selection (List α)) (s : Store B V) : Prop where
  input : s 11 = letters B V y
  label : s 12 = letters B V label
  index : (s 13).length = n
  random : s 17 = bits.map Symbol.bit
  empty : s 14 = []
  selection : SelectionStored B V s selection

namespace SearchStored

variable {B V} {n : ℕ} {y label : List α} {bits : BitString}
    {selection : BoundedTrialChoice.Selection (List α)} {s : Store B V}

theorem counter_pop (h : SearchStored B V n y label bits selection s) :
    SearchStored B V n y label bits selection ((Local.pop (23 : Fin 35)).eval s) := by
  rcases h with ⟨hi, hl, hn, hr, he, hc, hk, hf⟩
  constructor <;> simp_all [Local.eval_pop, SelectionStored]

end SearchStored

/-- A clocked inverse call preserves the caller inputs and returns exactly the
source evaluator's accepted value. It consumes its entire assigned block. -/
theorem inverseTrial_view (seed time : PolynomialBound) (n : ℕ) (y label : List α) (bits : BitString)
    (selection : BoundedTrialChoice.Selection (List α)) (s : Store B V)
    (stored : SearchStored B V n y label bits selection s) :
    ∃ (status : Source.Status (Fin V.states)) (output : List α),
      let next := (inverseTrial B V seed time).eval s
      SearchStored B V n y label (bits.drop (seed n)) selection next ∧
      next 0 = [.inverse (.state status)] ∧
      next 10 = output.map (fun a => Symbol.inverse (Source.Cell.output a)) ∧
      positiveResult V label status output = positiveValue V time n y label (bits.take (seed n)) := by
  obtain ⟨status, output, state, result, native⟩ := sourceTrial_result B V V Symbol.inverse (inverseDecode B V)
    (fun _ => rfl) (inverseInput B V) (inverseAuxiliary B V) (inverseBit B V) (fun _ => rfl)
    seed time s {input := y, auxiliary := label, index := n} bits
    (by simp [stored.input, letters, List.map_map, Function.comp_def, inverseInput])
    (by simp [stored.label, letters, List.map_map, Function.comp_def, inverseAuxiliary])
    stored.index stored.random stored.empty
  have outside (j : Fin 35) (large : 11 ≤ j.val) (clock : j ≠ 16) :=
    sourceTrial_outside B V V Symbol.inverse (inverseDecode B V) (inverseInput B V) (inverseAuxiliary B V)
      (inverseBit B V) seed time s j large clock
  refine ⟨status, output, ?_, state, result, positiveResult_eq V time n y label output _ status native⟩
  constructor
  · simpa [inverseTrial, trialPrepared] using (outside 11 (by decide) (by decide)).trans stored.input
  · simpa [inverseTrial, trialPrepared] using (outside 12 (by decide) (by decide)).trans stored.label
  · have eq := outside 13 (by decide) (by decide)
    simpa [inverseTrial, trialPrepared] using (congrArg List.length eq).trans stored.index
  · simpa [inverseTrial, trialPrepared, stored.random, stored.index, List.map_drop] using outside 17 (by decide) (by decide)
  · simpa [inverseTrial] using outside 14 (by decide) (by decide)
  · rcases stored.selection with ⟨candidate, locked, found⟩
    exact ⟨(sourceTrial_fixes B V V _ _ _ _ _ seed time 25 (by decide) s).trans candidate,
      (sourceTrial_fixes B V V _ _ _ _ _ seed time 26 (by decide) s).trans locked,
      (sourceTrial_fixes B V V _ _ _ _ _ seed time 27 (by decide) s).trans found⟩

end ComplexityOfGenerators.Simulation.ExactRecursive
