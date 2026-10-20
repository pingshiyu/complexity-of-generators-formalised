import ComplexityOfGenerators.Simulation.ExactRecursive.Program
import ComplexityOfGenerators.Simulation.ExactRecursive.TrialBounds
import ComplexityOfGenerators.Proofs.CommandGenerators

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def preparedMemory (n read : ℕ) (bits : BitString) : Memory (Cell B V) α 35 :=
  ⟨(), n, read, [], Function.update
    (Function.update (Function.update (fun _ => []) 13 (List.replicate n Symbol.unit))
      19 (List.replicate (n + 1) Symbol.unit)) 17 (bits.map Symbol.bit)⟩

noncomputable def prepareBudget (seed : PolynomialBound) (n : ℕ) : ℕ :=
  29 * n + 12 * seed n + Command.counterBudget seed n + 12

theorem prepare_runs (seed : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∃ t ≤ prepareBudget seed n,
      (prepareCommand B V seed).Runs n bits Command.emptyMemory t
        (if seed n ≤ bits.length then .done (preparedMemory B V n (seed n) (bits.take (seed n))) else .exhausted) := by
  let loaded : Memory (Cell B V) α 35 := Command.loadedIndex 13 Symbol.unit n Command.emptyMemory
  let seeded : Memory (Cell B V) α 35 := {loaded with store := (counter B V 18 (by decide) seed).eval loaded.store}
  have loadRun := Command.loadIndex_runs (13 : Fin 35) (Symbol.unit : Cell B V) n bits (Command.emptyMemory (O := α)) (Nat.zero_le _)
  have loadIndex : loaded.indexHead ≤ n := le_rfl
  obtain ⟨ticks, tickBound, counterRun⟩ := (counter B V 18 (by decide) seed).runs bits loaded loadIndex
  have loadSize : StoreBound loaded.store n := by
    intro j
    simp [loaded, Command.loadedIndex, Command.emptyMemory, Memory.set, Function.update_apply]
    split <;> simp
  have counterCost := CounterRoutine.routine_cost (O := α) (counterSlots 18 (by decide)) seed
    (Symbol.unit : Cell B V) loaded.store n loadSize
  have count_eq : (seeded.store 18).length = seed n := by
    simp [seeded, loaded, counter, CounterRoutine.routine_eval, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have head_eq : seeded.randomHead = 0 := rfl
  have seededIndex : seeded.indexHead ≤ n := le_rfl
  have size_eq : (loaded.store 13).length = n := by
    simp [loaded, Command.loadedIndex, Command.emptyMemory, Memory.set]
  change (counter B V 18 (by decide) seed).cost loaded.store ≤ _ at counterCost
  simp only [counterSlots_apply, size_eq] at counterCost
  by_cases enough : seed n ≤ bits.length
  · have collectRun := Command.collect_full 18 34 (by decide) (Symbol.bit : Bool → Cell B V)
      bits seeded seededIndex (by simpa [head_eq, count_eq] using enough)
    let collected := Command.collected 18 34 (Symbol.bit : Bool → Cell B V) bits seeded (seeded.store 18).length
    have collectedIndex : collected.indexHead ≤ n := le_rfl
    have transferRun := Command.transfer_runs 34 17 (by decide) (id : Cell B V → Cell B V) bits collected collectedIndex
    have collectedLength : (collected.store 34).length = seed n := by
      simp [collected, Command.collected, seeded, loaded, counter, CounterRoutine.routine_eval,
        Command.loadedIndex, Command.emptyMemory, Memory.set, head_eq, count_eq, Nat.min_eq_left enough]
    have final_eq : (collected.set 34 []).set 17 ((collected.store 34).reverse.map id ++ collected.store 17) =
        preparedMemory B V n (seed n) (bits.take (seed n)) := by
      apply Configuration.ext <;> try rfl
      · simp [collected, Command.collected, head_eq, count_eq, preparedMemory]
      · funext j
        fin_cases j <;>
          simp [collected, Command.collected, seeded, loaded, counter, CounterRoutine.routine_eval,
            Command.loadedIndex, Command.emptyMemory, Memory.set, preparedMemory, head_eq, count_eq,
            List.map_reverse]
    rw [final_eq, collectedLength] at transferRun
    have collectedRun := Command.Runs.seq _ _ _ _ _ _ _ collectRun transferRun
    have seededRun := Command.Runs.seq _ _ _ _ _ _ _ counterRun collectedRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun seededRun
    refine ⟨3 * n + 1 + (ticks + 1 + (6 * (seeded.store 18).length + 1 + 6 * seed n)), ?_, ?_⟩
    · change 3 * (n - 0) + 1 + (ticks + 1 + (6 * (seeded.store 18).length + 1 + 6 * seed n)) ≤ _
      rw [count_eq]
      dsimp only [prepareBudget]
      omega
    · simpa only [prepareCommand, enough, ite_true, Nat.sub_zero] using run
  · obtain ⟨t, cost, collectRun⟩ := Command.collect_short 18 34 (by decide) (Symbol.bit : Bool → Cell B V)
      bits seeded seededIndex (by simp only [head_eq, count_eq]; omega)
    have aborted := Command.Runs.seq_absent seeded (Command.collect 18 34 Symbol.bit)
      (Command.transfer 34 17 id) t collectRun
    have seededRun := Command.Runs.seq _ _ _ _ _ _ _ counterRun aborted
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun seededRun
    refine ⟨3 * n + 1 + (ticks + 1 + t), ?_, ?_⟩
    · simp only [count_eq] at cost
      change 3 * (n - 0) + 1 + (ticks + 1 + t) ≤ _
      dsimp only [prepareBudget]
      omega
    · simpa only [prepareCommand, enough, ite_false, Nat.sub_zero] using run

end ComplexityOfGenerators.Simulation.ExactRecursive
