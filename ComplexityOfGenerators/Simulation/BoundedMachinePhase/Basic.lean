import ComplexityOfGenerators.Simulation.UnionGenerator.Views
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Views
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Components

namespace ComplexityOfGenerators.Simulation.BoundedMachinePhase

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

abbrev Cell := UnionGenerator.Cell M M
abbrev Store := Local.Store (Cell M) 35
abbrev Controller := WordStack.Routine (Cell M) α 35

def prepare : Controller M :=
  (WordStack.Routine.assign 22 13 33 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)).seq
    (WordStack.Routine.clearMany [11, 12, 14, 31, 32])

def finish : Controller M :=
  WordStack.Routine.branch 0 fun status => match status with
    | some (.left (.state .accepted)) =>
      (UnionGenerator.takeOutput M M 31 (by decide) (UnionGenerator.leftOutput M M)).seq
        (UnionGenerator.flag M M 32 true)
    | _ => (WordStack.Routine.clear 31).seq (UnionGenerator.flag M M 32 false)

noncomputable def phase (seed clock : PolynomialBound) : Controller M :=
  (prepare M).seq ((UnionGenerator.leftTrial M M seed clock).seq (finish M))

theorem prepare_fixes22 : (prepare M).Fixes 22 := by
  intro s
  simp [prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]

theorem finish_fixes22 : (finish M).Fixes 22 := by
  intro s
  simp only [finish, WordStack.Routine.branch]
  split <;> simp [WordStack.Routine.seq, UnionGenerator.takeOutput_eval,
    UnionGenerator.flag_eval, WordStack.Routine.clear]

theorem phase_fixes22 (seed clock : PolynomialBound) : (phase M seed clock).Fixes 22 :=
  (prepare_fixes22 M).seq
  ((ConcatenationGenerator.sourceTrial_fixes_outer M M M Symbol.left (UnionGenerator.leftDecode M M)
    (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit M M) seed clock 22 (by decide)).seq
    (finish_fixes22 M))

theorem phase_correct (seed clock : PolynomialBound) :
    FixedBlockRetry.PhaseCorrect (Symbol.unit : Cell M) Symbol.bit (UnionGenerator.outputLetter M M)
      seed (phase M seed clock) (fun n bits => UnionGenerator.sourceValue M clock n bits) := by
  intro n block s length _ master random
  let r := (prepare M).eval s
  have ri : r 11 = [] := by simp [r, prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]
  have ra : r 12 = [] := by simp [r, prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]
  have re : r 14 = [] := by simp [r, prepare, WordStack.Routine.seq, WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval]
  have rn : (r 13).length = n := by simpa [r, prepare, WordStack.Routine.seq,
    WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval] using master
  have rr : r 17 = block.map Symbol.bit := by simpa [r, prepare, WordStack.Routine.seq,
    WordStack.Routine.assign_eval, WordStack.Routine.clearMany_eval] using random
  obtain ⟨status, output, state, payload, native⟩ :=
    BoundedSource.sourceTrial_result (O := α) Symbol.unit Symbol.bit M Symbol.left (UnionGenerator.leftDecode M M)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit M M) (fun _ => rfl)
      seed clock r (generatorData n) block
      (by simp [ri, generatorData]) (by simp [ra, generatorData]) rn rr re
  change ∀ word, (status = .accepted ∧ output.reverse = word) ↔
    M.run (generatorData n) (block.take (seed n)) (clock n) = .halted (.accepted word) at native
  have whole : block.take (seed n) = block := by rw [← length, List.take_length]
  rw [whole] at native
  let t := (UnionGenerator.leftTrial M M seed clock).eval r
  change t 0 = [.left (.state status)] at state
  change t 10 = output.map (fun a => Symbol.left (Source.Cell.output a)) at payload
  have value : UnionGenerator.sourceValue M clock n block =
      (if status = .accepted then some output.reverse else none) := by
    apply Option.ext
    intro word
    rw [UnionGenerator.sourceValue_eq_some, ← native]
    by_cases accepted : status = .accepted <;> simp [accepted]
  change ((finish M).eval t 32 = FixedBlockRetry.flagWord Symbol.unit
      (UnionGenerator.sourceValue M clock n block).isSome ∧
    ∀ word, UnionGenerator.sourceValue M clock n block = some word →
      ((finish M).eval t 31).filterMap (UnionGenerator.outputLetter M M) = word)
  rw [value]
  cases status <;>
    simp [finish, WordStack.Routine.branch, WordStack.Routine.seq, state, payload,
      UnionGenerator.takeOutput_eval, UnionGenerator.flag_eval, WordStack.Routine.clear,
      FixedBlockRetry.flagWord, UnionGenerator.flagWord, UnionGenerator.leftOutput,
      List.map_reverse, List.map_map, List.filterMap_map, Function.comp_def, UnionGenerator.outputLetter]

end ComplexityOfGenerators.Simulation.BoundedMachinePhase
