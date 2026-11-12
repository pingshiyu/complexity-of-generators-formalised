import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Sample
import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Check
import ComplexityOfGenerators.Simulation.WordStack.Unary
import ComplexityOfGenerators.Simulation.WordStack.Routines
import ComplexityOfGenerators.Proofs.CommandGenerators

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack
set_option backward.isDefEq.respectTransparency false

def copyClock : Routine Symbol Symbol 35 := Routine.copy 32 33 31 (by decide) (by decide) (by decide) id

def orient : Routine Symbol Symbol 35 := Routine.transfer 34 2 (by decide) id

def save : Routine Symbol Symbol 35 := Routine.assign 2 34 33 (by decide) (by decide) (by decide) id

def prepare : Code :=
  (Command.loadIndex 32 .zero).seq (copyClock.command.seq
    ((sample 33 34).seq (orient.command.seq save.command)))

def preparedStore (n : ℕ) (word : List Symbol) : Store :=
  Function.update (Function.update (Function.update (fun _ => []) 32 (List.replicate n .zero)) 2 word) 34 word

def preparedMemory (n : ℕ) (bits : BitString) : Memory :=
  ⟨(), n, 4*n, [], preparedStore n (decodeWords n bits)⟩

theorem prepared_bound (n : ℕ) (bits : BitString) : StoreBound (preparedMemory n bits).store n := by
  intro j
  by_cases a : j = 32 <;> by_cases b : j = 2 <;> by_cases c : j = 34 <;>
    simp [preparedMemory, preparedStore, a, b, c]

theorem prepare_full (n : ℕ) (bits : BitString) (available : 4*n ≤ bits.length) :
    ∃ ticks ≤ 50*n+20, prepare.Runs n bits Command.emptyMemory ticks (.done (preparedMemory n bits)) := by
  let loaded : Memory := Command.loadedIndex 32 .zero n Command.emptyMemory
  let copied : Memory := {loaded with store := copyClock.eval loaded.store}
  let sampledMemory := sampled 33 34 n bits copied
  let oriented : Memory := {sampledMemory with store := orient.eval sampledMemory.store}
  have load := Command.loadIndex_runs (O := Symbol) (32 : Fin 35) Symbol.zero n bits Command.emptyMemory (Nat.zero_le _)
  obtain ⟨copyTicks, copyBound, copyRun⟩ := copyClock.runs (n := n) bits loaded le_rfl
  have copyCost : copyClock.cost loaded.store = 14*n+2 := by
    simp [copyClock, Routine.copy, loaded, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have clock : copied.store 33 = List.replicate n .zero := by
    simp [copied, loaded, copyClock, Routine.copy, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have randomHead : copied.randomHead = 0 := rfl
  have sampleRun := sample_full 33 34 (by decide) n bits copied le_rfl (by
    simpa only [randomHead, Nat.zero_add, clock, List.length_replicate] using available)
  rw [clock, List.length_replicate] at sampleRun
  obtain ⟨orientTicks, orientBound, orientRun⟩ := orient.runs (n := n) bits sampledMemory le_rfl
  have sampleWord : sampledMemory.store 34 = (decodeWords n bits).reverse := by
    simp [sampledMemory, sampled, copied, loaded, copyClock, Routine.copy,
      Command.loadedIndex, Command.emptyMemory, Memory.set]
  have orientCost : orient.cost sampledMemory.store = 6*n := by simp [orient, Routine.transfer, sampleWord]
  obtain ⟨saveTicks, saveBound, saveRun⟩ := save.runs (n := n) bits oriented le_rfl
  have orientFields : oriented.store 2 = decodeWords n bits ∧ oriented.store 34 = [] ∧ oriented.store 33 = [] := by
    simp [oriented, orient, Routine.transfer, sampleWord, sampledMemory, sampled, copied, loaded,
      copyClock, Routine.copy, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have saveCost : save.cost oriented.store = 14*n+3 := by
    simp [save, Routine.assign_cost, orientFields.1, orientFields.2.1, orientFields.2.2]
  have final : {oriented with store := save.eval oriented.store} = preparedMemory n bits := by
    apply Configuration.ext <;> try rfl
    · simp [oriented, sampledMemory, sampled, copied, loaded, preparedMemory, Command.loadedIndex, Command.emptyMemory, Memory.set]
    · funext j
      fin_cases j <;>
        simp [oriented, sampledMemory, sampled, copied, loaded, preparedMemory, preparedStore,
          save, orient, copyClock, Routine.assign_eval, Routine.transfer, Routine.copy,
          Command.loadedIndex, Command.emptyMemory, Memory.set]

  rw [final] at saveRun
  have run := Command.Runs.seq _ _ _ _ _ _ _ load
    (Command.Runs.seq _ _ _ _ _ _ _ copyRun
      (Command.Runs.seq _ _ _ _ _ _ _ sampleRun
        (Command.Runs.seq _ _ _ _ _ _ _ orientRun saveRun)))
  refine ⟨3*n+1+(copyTicks+1+(9*n+1+(orientTicks+1+saveTicks))), ?_, ?_⟩
  · omega
  · simpa only [prepare, Nat.sub_zero] using run

theorem prepare_short (n : ℕ) (bits : BitString) (short : bits.length < 4*n) :
    ∃ ticks ≤ 50*n+20, prepare.Runs n bits Command.emptyMemory ticks .exhausted := by
  let loaded : Memory := Command.loadedIndex 32 .zero n Command.emptyMemory
  let copied : Memory := {loaded with store := copyClock.eval loaded.store}
  have load := Command.loadIndex_runs (O := Symbol) (32 : Fin 35) Symbol.zero n bits Command.emptyMemory (Nat.zero_le _)
  obtain ⟨copyTicks, copyBound, copyRun⟩ := copyClock.runs (n := n) bits loaded le_rfl
  have copyCost : copyClock.cost loaded.store = 14*n+2 := by
    simp [copyClock, Routine.copy, loaded, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have clock : copied.store 33 = List.replicate n .zero := by
    simp [copied, loaded, copyClock, Routine.copy, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have randomHead : copied.randomHead = 0 := rfl
  obtain ⟨sampleTicks, sampleBound, sampleRun⟩ := sample_short 33 34 (by decide) n bits copied le_rfl
    (by change 0 ≤ bits.length; omega) (by
      simpa only [randomHead, Nat.zero_add, clock, List.length_replicate] using short)
  rw [clock, List.length_replicate] at sampleBound
  have absent := Command.Runs.seq_absent copied (sample 33 34) (orient.command.seq save.command) sampleTicks sampleRun
  have run := Command.Runs.seq _ _ _ _ _ _ _ load (Command.Runs.seq _ _ _ _ _ _ _ copyRun absent)
  exact ⟨3*n+1+(copyTicks+1+sampleTicks), by omega, by simpa only [prepare, Nat.sub_zero] using run⟩

end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
