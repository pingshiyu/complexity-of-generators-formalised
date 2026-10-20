import ComplexityOfGenerators.Simulation.ExactRecursive.Body
import ComplexityOfGenerators.Simulation.ClockProgress

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem finish_runs (n : ℕ) (bits rest : BitString) (m : Memory (Cell B V) α 35)
    (state : Walker α) (stored : WalkStored B V n state rest m.store)
    (target : m.store 30 = flagWord B V (decide (state.word.length = n)))
    (index : m.indexHead ≤ n) (output : m.output = []) :
    ∃ t ≤ 4 * state.word.length + 2 + bits.length, ∃ result,
      (finish B V).Runs n bits m t result ∧ result.outcome.acceptedWord = state.answer n := by
  by_cases valid : state.valid = true
  · by_cases equal : state.word.length = n
    · have emit := Command.emitWord_runs 11 (outputLetter B V) bits m index
      have inner : (Command.branch 30 fun t => if t.1.isSome then
          Command.emitWord 11 (outputLetter B V) else Command.drain).Runs n bits m
          (1 + 4 * (m.store 11).length) (.done (Command.emitted 11 (outputLetter B V) m)) := by
        apply Command.Runs.branch
        simpa [observe, target, equal, flagWord] using emit
      have outer : (finish B V).Runs n bits m (1 + (1 + 4 * (m.store 11).length))
          (.done (Command.emitted 11 (outputLetter B V) m)) := by
        apply Command.Runs.branch
        simpa [observe, stored.valid, valid, flagWord] using inner
      refine ⟨_, ?_, _, outer, ?_⟩
      · simp [stored.input, letters]
        omega
      · simp [Result.outcome, Outcome.acceptedWord, Command.emitted, output, stored.input,
          letters, List.filterMap_map, Function.comp_def, outputLetter, Walker.answer, valid, equal]
    · have inner : (Command.branch 30 fun t => if t.1.isSome then
          Command.emitWord 11 (outputLetter B V) else Command.drain).Runs n bits m
          (1 + (bits.length - m.randomHead)) .exhausted := by
        apply Command.Runs.branch
        simpa [observe, target, equal, flagWord] using Command.Runs.drain (n := n) (bits := bits) m
      have outer : (finish B V).Runs n bits m (1 + (1 + (bits.length - m.randomHead))) .exhausted := by
        apply Command.Runs.branch
        simpa [observe, stored.valid, valid, flagWord] using inner
      exact ⟨_, by omega, _, outer, by simp [Result.outcome, Outcome.acceptedWord, Walker.answer, equal]⟩
  · have outer : (finish B V).Runs n bits m (1 + (bits.length - m.randomHead)) .exhausted := by
      apply Command.Runs.branch
      simpa [observe, stored.valid, valid, flagWord] using Command.Runs.drain (n := n) (bits := bits) m
    exact ⟨_, by omega, _, outer, by simp [Result.outcome, Outcome.acceptedWord, Walker.answer, valid]⟩

end ComplexityOfGenerators.Simulation.ExactRecursive
