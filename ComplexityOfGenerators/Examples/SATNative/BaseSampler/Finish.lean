import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Default
import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Prepare
import ComplexityOfGenerators.Simulation.WordStack.FixedOutput

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] NativeEvaluation.verifier check

def emitProposal : Code := Command.emitWord 34 some

def fallback : Code := defaultRoutine.command.seq
  (.branch 33 fun observation => if observation.1.isSome then emitProposal else .drain)

/-- Three finite observations implement the verifier's Boolean verdict. -/
def dispatch (yes no : Code) : Code :=
  .branch 2 fun word => .branch 17 fun inside => .branch 6 fun valid =>
    if !word.1.isSome && !inside.1.isSome && valid.1.isSome then yes else no

def finish : Code := dispatch emitProposal fallback

def expectedOutcome (n : ℕ) (word : List Symbol) (good : Bool) : Outcome Symbol :=
  if good then .accepted word else if BaseProductive n then .accepted (baseDefault n) else .exhausted

theorem dispatch_runs (yes no : Code) (n : ℕ) (bits : BitString) (m : Memory)
    (ticks : ℕ) (result : Result Symbol Symbol 35)
    (run : (if verdict m.store then yes else no).Runs n bits m ticks result) :
    (dispatch yes no).Runs n bits m (3+ticks) result := by
  have predicate : (!(observe n m 2).1.isSome && !(observe n m 17).1.isSome &&
      (observe n m 6).1.isSome) = verdict m.store := by
    cases word : m.store 2 <;> simp [verdict, observe, word]
  rw [show 3+ticks = 1+(1+(1+ticks)) by omega]
  unfold dispatch
  apply Command.Runs.branch m 2 _ (1+(1+ticks)) result
  apply Command.Runs.branch m 17 _ (1+ticks) result
  apply Command.Runs.branch m 6 _ ticks result
  simpa only [predicate] using run

theorem emitProposal_runs (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (word : List Symbol) (saved : m.store 34 = word) (output : m.output = []) :
    ∃ result, emitProposal.Runs n bits m (4*word.length) result ∧ result.outcome = .accepted word := by
  have run := Command.emitWord_runs (34 : Fin 35) (some : Symbol → Option Symbol) bits m index
  refine ⟨.done (Command.emitted 34 some m), ?_, ?_⟩
  · simpa only [emitProposal, saved] using run
  · simp [Result.outcome, Command.emitted, output, saved]

theorem fallback_runs (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (counter : m.store 32 = List.replicate n .zero) (empty : m.store 33 = [])
    (proposal : (m.store 34).length ≤ n) (output : m.output = []) :
    ∃ ticks ≤ 30*n+bits.length+50, ∃ result,
      fallback.Runs n bits m ticks result ∧
        result.outcome = if BaseProductive n then .accepted (baseDefault n) else .exhausted := by
  obtain ⟨firstTicks, firstCost, firstRun⟩ := defaultRoutine.runs (n := n) bits m index
  let filled : Memory := {m with store := defaultRoutine.eval m.store}
  have cost := defaultRoutine_cost m.store n counter empty proposal
  have flag := defaultRoutine_flag m.store n counter empty
  by_cases productive : BaseProductive n
  · have word := defaultRoutine_value m.store n counter empty productive
    obtain ⟨result, emission, outcome⟩ := emitProposal_runs n bits filled index (baseDefault n) word output
    have last : (Command.branch 33 fun observation => if observation.1.isSome then emitProposal else .drain).Runs
        n bits filled (1+4*n) result := by
      apply Command.Runs.branch
      simpa only [observe, filled, flag, decide_eq_true productive, ite_true, baseDefault_length n productive] using emission
    have run := Command.Runs.seq m filled _ _ firstTicks (1+4*n) result firstRun last
    exact ⟨firstTicks+1+(1+4*n), by omega, result, run, by simpa [productive] using outcome⟩
  · have last : (Command.branch 33 fun observation => if observation.1.isSome then emitProposal else .drain).Runs
        n bits filled (1+(bits.length-filled.randomHead)) .exhausted := by
      apply Command.Runs.branch
      simpa only [observe, filled, flag, decide_eq_false productive, Bool.false_eq_true, ite_false] using Command.Runs.drain (n := n) (bits := bits) filled
    have run := Command.Runs.seq m filled _ _ firstTicks (1+(bits.length-filled.randomHead)) .exhausted firstRun last
    exact ⟨firstTicks+1+(1+(bits.length-filled.randomHead)), by omega, .exhausted, run, by simp [productive, Result.outcome]⟩

theorem finish_runs (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (word : List Symbol) (length : word.length = n) (saved : m.store 34 = word)
    (counter : m.store 32 = List.replicate n .zero) (empty : m.store 33 = [])
    (output : m.output = []) :
    ∃ ticks ≤ 30*n+bits.length+53, ∃ result,
      finish.Runs n bits m ticks result ∧ result.outcome = expectedOutcome n word (verdict m.store) := by
  cases good : verdict m.store with
  | false =>
      obtain ⟨ticks, bound, result, run, outcome⟩ := fallback_runs n bits m index counter empty (by simpa [saved, length]) output
      exact ⟨3+ticks, by omega, result, dispatch_runs _ _ n bits m ticks result (by simpa only [good, Bool.false_eq_true, ite_false] using run),
        by simpa only [expectedOutcome, good, Bool.false_eq_true, ite_false] using outcome⟩
  | true =>
      obtain ⟨result, run, outcome⟩ := emitProposal_runs n bits m index word saved output
      rw [length] at run
      exact ⟨3+4*n, by omega, result, dispatch_runs _ _ n bits m (4*n) result (by simpa only [good, ite_true] using run),
        by simpa only [expectedOutcome, good, ite_true] using outcome⟩

end
end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
