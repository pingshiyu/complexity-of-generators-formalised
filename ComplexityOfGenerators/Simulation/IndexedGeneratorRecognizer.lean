import ComplexityOfGenerators.Simulation.GuessedIndex
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

/-! A native recognizer for a generator family with polynomially bounded
producing indices and polynomially short accepting paths. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

def indexedGeneratorRecognizer : Machine α Bool Unit :=
  sequenceMachine (guessedIndexLoader M) (generatorMatcherRoutine M)

/-- The loader's final silent step and handoff are both charged. -/
theorem indexedGeneratorRecognizer_loaded (w : List α) (i : ℕ) (tail : BitString) :
    ∃ core : Configuration (virtualIndexCore M),
      IndexReady M i (M.shiftRandomConfiguration (indexChoice i) M.initialConfiguration) false core ∧
      (indexedGeneratorRecognizer M).run (decisionData w) (indexChoice i ++ tail) (3 * i + 4) =
        (indexedGeneratorRecognizer M).observe (decisionData w) (indexChoice i ++ tail)
          (sequenceRightConfiguration (guessedIndexLoader M) (generatorMatcherRoutine M)
            (matcherConfiguration (virtualIndexCore M) w core)) := by
  let L := guessedIndexLoader M
  let routine := generatorMatcherRoutine M
  let C := indexedGeneratorRecognizer M
  let data := decisionData w
  let bits := indexChoice i ++ tail
  obtain ⟨ready, state, head, random, input, auxiliary, index, output, memory, loaded⟩ :=
    guessedIndex_loaded M w i tail
  have table : L.transition ready.state data.input[ready.inputHead]? data.auxiliary[ready.auxiliaryHead]?
      (if ready.indexHead < data.index then some () else none) (ready.work ready.workHead) =
      .step (4 : Fin 5) none .stay .stay .stay .stay none := by
    simp [L, guessedIndexLoader, state, head, memory _, virtualIndexCell]
  have live := L.observe_step data bits ready _ _ _ _ _ _ _ table
  have next := L.next_step data bits ready _ _ _ _ _ _ _ table
  let done := L.stepConfiguration data ready (4 : Fin 5) none .stay .stay .stay .stay none
  have accepts : L.transition done.state data.input[done.inputHead]? data.auxiliary[done.auxiliaryHead]?
      (if done.indexHead < data.index then some () else none) (done.work done.workHead) = .accept := by
    simp [L, guessedIndexLoader, done, Machine.stepConfiguration]
  let target := handoffConfiguration L routine data done []
  let core : Configuration (virtualIndexCore M) := {
    state := (virtualIndexCore M).initial
    inputHead := 0
    auxiliaryHead := 0
    indexHead := 0
    randomHead := i + 1
    workHead := 0
    work := ready.work
    visited := target.visited
    output := [] }
  have related : IndexReady M i (M.shiftRandomConfiguration (indexChoice i) M.initialConfiguration) false core := by
    refine ⟨⟨memory, ?_, rfl⟩, rfl, rfl, by simp [Machine.shiftRandomConfiguration, Machine.initialConfiguration]⟩
    simp [core, Machine.shiftRandomConfiguration, Machine.initialConfiguration, indexChoice]
  have targetEq : target = matcherConfiguration (virtualIndexCore M) w core := by
    simp [target, handoffConfiguration, done, Machine.stepConfiguration, head, input, auxiliary, index, random,
      Move.onInput, Move.onInt, core, matcherConfiguration, routine, generatorMatcherRoutine, machineRoutine, outputMatcher]
  have lifted := sequence_left_running L routine data bits L.initialConfiguration ready [] (3 * i + 2)
    (by simpa [live, L, data, bits] using loaded)
  have initial : sequenceLeftConfiguration L routine L.initialConfiguration [] = C.initialConfiguration := rfl
  rw [initial] at lifted
  have loadedPrefix : C.runFrom data bits C.initialConfiguration (3 * i + 2) =
      C.observe data bits (sequenceLeftConfiguration L routine ready []) := by
    exact lifted.trans (sequence_left_observe L routine data bits ready [] live).symm
  have liftedLive := sequence_left_observe L routine data bits ready [] live
  have liftedNext := sequence_left_next L routine data bits ready done [] next
  have step : C.runFrom data bits (sequenceLeftConfiguration L routine ready []) 1 =
      C.observe data bits (sequenceLeftConfiguration L routine done []) :=
    C.runFrom_shift data bits _ _ liftedLive liftedNext 0
  have handoff := sequence_accept_handoff L routine data bits done [] accepts
  refine ⟨core, related, ?_⟩
  change C.run data bits _ = _
  rw [show 3 * i + 4 = (3 * i + 2) + (1 + 1) by omega, ← C.runFrom_initial,
    C.runFrom_add data bits C.initialConfiguration _ _ loadedPrefix,
    C.runFrom_add data bits _ _ 1 step]
  exact handoff.trans (congrArg (fun c => C.observe data bits (sequenceRightConfiguration L routine c)) targetEq)

/-- Every source outcome is preserved, including its exact output comparison. -/
theorem indexedGeneratorRecognizer_run (w : List α) (i t : ℕ) (tail : BitString) (result : Outcome α)
    (execution : M.run (generatorData i) tail t = .halted result) :
    ∃ ticks, ticks ≤ 3 * i + 4 + (t + 1) * (2 * (i + 1 + t) + 2 * i + 8) ∧
      (indexedGeneratorRecognizer M).run (decisionData w) (indexChoice i ++ tail) ticks =
        .halted (matcherOutcome w result) := by
  let data := decisionData w
  let bits := indexChoice i ++ tail
  let source := M.shiftRandomConfiguration (indexChoice i) M.initialConfiguration
  obtain ⟨core, related, loaded⟩ := indexedGeneratorRecognizer_loaded M w i tail
  have resources : M.ConfigurationBound (generatorData i) (i + 1) source := by
    constructor <;> simp [source, Machine.shiftRandomConfiguration, Machine.initialConfiguration, generatorData, indexChoice]
    omega
  have shifted : M.runFrom (generatorData i) bits source t = .halted result := by
    rw [Machine.runFrom_shift_random, Machine.runFrom_initial, execution]
    rfl
  obtain ⟨ticks, bound, simulated⟩ := index_simulates_runFrom M (matcherSourceData data) bits i t (i + 1)
    source false core related resources result shifted
  have matched := outputMatcher_runFrom (virtualIndexCore M) data bits core ticks
  rw [simulated] at matched
  change (outputMatcher (virtualIndexCore M)).runFrom data bits
    (matcherConfiguration (virtualIndexCore M) w core) ticks = .halted (matcherOutcome w result) at matched
  have lifted := sequence_right_runFrom (guessedIndexLoader M) (generatorMatcherRoutine M) data bits
    (matcherConfiguration (virtualIndexCore M) w core) ticks
  change (indexedGeneratorRecognizer M).runFrom data bits
    (sequenceRightConfiguration (guessedIndexLoader M) (generatorMatcherRoutine M) _ ) ticks =
      sequenceRightResult (guessedIndexLoader M) (generatorMatcherRoutine M)
        ((outputMatcher (virtualIndexCore M)).runFrom data bits
          (matcherConfiguration (virtualIndexCore M) w core) ticks) at lifted
  rw [matched] at lifted
  rw [← (indexedGeneratorRecognizer M).runFrom_initial] at loaded
  refine ⟨3 * i + 4 + ticks, Nat.add_le_add_left bound _, ?_⟩
  rw [← (indexedGeneratorRecognizer M).runFrom_initial,
    (indexedGeneratorRecognizer M).runFrom_add data bits _ _ (3 * i + 4) loaded]
  exact lifted

end
end ComplexityOfGenerators.Simulation
