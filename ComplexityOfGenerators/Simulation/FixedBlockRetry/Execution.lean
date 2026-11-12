import ComplexityOfGenerators.Simulation.FixedBlockRetry.Loop
import ComplexityOfGenerators.Proofs.CommandGenerators
import ComplexityOfGenerators.Proofs.FixedBlockRetryCriteria
import ComplexityOfGenerators.Foundations.FixedBlockPrefix

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S O : Type} [Fintype S] (unitSymbol : S) (bitSymbol : Bool → S)

def loadedStore (n : ℕ) : Local.Store S 35 :=
  Function.update (fun _ => []) 13 (List.replicate n unitSymbol)

def readyStore (n : ℕ) : Local.Store S 35 :=
  Function.update (loadedStore unitSymbol n) 22 (List.replicate n unitSymbol)

def readyMemory (n : ℕ) : Memory S O 35 := ⟨(), n, 0, [], readyStore unitSymbol n⟩

theorem setup_eval (n : ℕ) :
    (setup (O := O) unitSymbol).eval (loadedStore unitSymbol n) = readyStore unitSymbol n := by
  funext j
  by_cases h13 : j = 13 <;> by_cases h22 : j = 22 <;> by_cases h33 : j = 33 <;>
    by_cases h31 : j = 31 <;> by_cases h32 : j = 32 <;>
      simp [setup, Routine.seq, Routine.assign_eval, Routine.clear, loadedStore, readyStore,
        Function.update_apply, h13, h22, h33, h31, h32]

theorem setup_cost (n : ℕ) : (setup (O := O) unitSymbol).cost (loadedStore unitSymbol n) ≤ 14*n+5 := by
  simp [setup, Routine.seq, Routine.assign_cost, Routine.assign_eval, Routine.clear, loadedStore]

theorem ready_state (n cap : ℕ) (indexBudget : n+1 ≤ cap) :
    State n cap (readyMemory (O := O) unitSymbol n) := by
  refine ⟨le_refl n, by simp [readyMemory, readyStore, loadedStore],
    by simp [readyMemory, readyStore], rfl, ?_⟩
  intro j
  by_cases h13 : j = 13 <;> by_cases h22 : j = 22 <;>
    simp [readyMemory, readyStore, loadedStore, h13, h22] <;> omega

variable (decode : S → Option O) (width cap time : PolynomialBound)
    (phase : WordStack.Routine S O 35) (f : ℕ → BitString → Option (List O))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase) (frame : ∀ s, (phase.eval s 22).length = (s 22).length)

include correct bounded frame in
theorem command_runs (n : ℕ) (bits : BitString) (indexBudget : n+1 ≤ cap n)
    (widthBudget : width n ≤ cap n) :
    ∃ t ≤ 17*n+8+loopBudget width cap time n (bits.length / width n)+4*cap n, ∃ result,
      (command unitSymbol bitSymbol decode width phase).Runs n bits Command.emptyMemory t result ∧
      result.outcome.acceptedWord = value width f n bits := by
  let loaded := Command.loadedIndex (O := O) (13 : Fin 35) unitSymbol n Command.emptyMemory
  have load := Command.loadIndex_runs (O := O) (13 : Fin 35) unitSymbol n bits Command.emptyMemory (Nat.zero_le n)
  have initial : loaded.store = loadedStore unitSymbol n := by
    simp [loaded, Command.loadedIndex, Command.emptyMemory, Memory.set, loadedStore]
  obtain ⟨setupTime, setupTicks, setupRun⟩ := (setup (O := O) unitSymbol).runs (n := n) bits loaded (le_refl n)
  have setupCost : setupTime ≤ 14*n+5 := by rw [initial] at setupTicks; exact setupTicks.trans (setup_cost unitSymbol n)
  have ready : {loaded with store := (setup (O := O) unitSymbol).eval loaded.store} = readyMemory unitSymbol n := by
    rw [initial, setup_eval]
    rfl
  rw [ready] at setupRun
  obtain ⟨loopTime, loopTicks, result, loopRun, answer, finished⟩ :=
    loop_runs unitSymbol bitSymbol width cap time phase decode f correct bounded frame n (bits.length / width n)
      bits (readyMemory unitSymbol n) (ready_state unitSymbol n (cap n) indexBudget)
      (by simp [readyMemory, readyStore, loadedStore]) indexBudget widthBudget (by simp [readyMemory])
  have answer' : selected decode result = value width f n bits := by simpa [value, readyMemory] using answer
  cases result with
  | exhausted =>
    have rest := Command.Runs.seq_absent (readyMemory unitSymbol n) _ (Command.emitWord 31 decode) loopTime loopRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ load (Command.Runs.seq _ _ _ _ _ _ _ setupRun rest)
    refine ⟨3*n+1+(setupTime+1+loopTime), by omega, .exhausted, ?_, ?_⟩
    · simpa only [command, Nat.sub_zero] using run
    · exact answer'
  | done next =>
    obtain ⟨nextState, _⟩ := finished
    have emit := Command.emitWord_runs (31 : Fin 35) decode bits next nextState.head
    have run := Command.Runs.seq _ _ _ _ _ _ _ load
      (Command.Runs.seq _ _ _ _ _ _ _ setupRun (Command.Runs.seq _ _ _ _ _ _ _ loopRun emit))
    refine ⟨3*n+1+(setupTime+1+(loopTime+1+4*(next.store 31).length)), ?_, .done (Command.emitted 31 decode next), ?_, ?_⟩
    · have := nextState.sizes 31
      omega
    · simpa only [command, Nat.sub_zero] using run
    · simpa [Result.outcome, Outcome.acceptedWord, Command.emitted, nextState.output, selected] using answer'

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
