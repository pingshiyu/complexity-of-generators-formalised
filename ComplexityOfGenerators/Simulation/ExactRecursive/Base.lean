import ComplexityOfGenerators.Simulation.ExactRecursive.WalkView

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def baseValue (time : PolynomialBound) (n : ℕ) (bits : BitString) : Option (List α) :=
  match B.run (generatorData n) bits (time n) with
  | .halted (.accepted word) => some word
  | _ => none

def baseState : Option (List α) → Walker α
  | none => ⟨[], false, false⟩
  | some word => ⟨word, true, false⟩

theorem baseValue_eq_some (time : PolynomialBound) (n : ℕ) (bits : BitString) (word : List α) :
    baseValue B time n bits = some word ↔
      B.run (generatorData n) bits (time n) = .halted (.accepted word) := by
  unfold baseValue
  cases B.run (generatorData n) bits (time n) with
  | running c => simp
  | halted outcome => cases outcome <;> simp

theorem baseTrial_view (seed time : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store B V)
    (input : s 11 = []) (auxiliary : s 12 = []) (index : (s 13).length = n)
    (random : s 17 = bits.map Symbol.bit) (empty : s 14 = []) (stopped : s 28 = []) :
    WalkStored B V n (baseState (baseValue B time n (bits.take (seed n)))) (bits.drop (seed n))
      ((baseFinish B V).eval ((baseTrial B V seed time).eval s)) := by
  obtain ⟨status, output, state, result, native⟩ := sourceTrial_result B V B Symbol.base (baseDecode B V)
    (fun _ => rfl) (fun _ => .base .unit) (fun _ => .base .unit) (baseBit B V) (fun _ => rfl)
    seed time s (generatorData n) bits (by simp [input, generatorData]) (by simp [auxiliary, generatorData])
    index random empty
  let t := (baseTrial B V seed time).eval s
  have outside (j : Fin 35) (large : 11 ≤ j.val) (clock : j ≠ 16) :=
    sourceTrial_outside B V B Symbol.base (baseDecode B V) (fun _ => .base .unit) (fun _ => .base .unit)
      (baseBit B V) seed time s j large clock
  have ti : t 11 = [] := by simpa [t, baseTrial, trialPrepared, input] using outside 11 (by decide) (by decide)
  have tn : (t 13).length = n := by
    simpa [t, baseTrial, trialPrepared, index] using congrArg List.length (outside 13 (by decide) (by decide))
  have tr : t 17 = (bits.drop (seed n)).map Symbol.bit := by
    simpa [t, baseTrial, trialPrepared, random, index, List.map_drop] using outside 17 (by decide) (by decide)
  have te : t 14 = [] := by simpa [t, baseTrial] using outside 14 (by decide) (by decide)
  have ts : t 28 = [] := by simpa [t, baseTrial, trialPrepared, stopped] using outside 28 (by decide) (by decide)
  change ∀ word, (status = .accepted ∧ output.reverse = word) ↔
    B.run (generatorData n) (bits.take (seed n)) (time n) = .halted (.accepted word) at native
  have val : baseValue B time n (bits.take (seed n)) =
      (if status = .accepted then some output.reverse else none) := by
    apply Option.ext
    intro word
    rw [baseValue_eq_some, ← native]
    by_cases h : status = .accepted <;> simp [h]
  change t 0 = [.base (.state status)] at state
  change t 10 = output.map (fun a => Symbol.base (Source.Cell.output a)) at result
  change WalkStored B V n _ _ ((baseFinish B V).eval t)
  rw [val]
  cases status <;>
    constructor <;>
    simp_all [baseFinish, WordStack.Routine.branch, WordStack.Routine.seq,
      takeOutput_eval, flag_eval, flagWord, baseState, letters, baseOutput,
      List.map_map, Function.comp_def, List.map_reverse]

end ComplexityOfGenerators.Simulation.ExactRecursive
