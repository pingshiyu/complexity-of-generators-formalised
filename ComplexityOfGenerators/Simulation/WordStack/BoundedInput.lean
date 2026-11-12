import ComplexityOfGenerators.Simulation.WordStack.BoundedSource
import ComplexityOfGenerators.Simulation.WordStack.Unary
import ComplexityOfGenerators.Simulation.WordStack.RandomInput
import ComplexityOfGenerators.Proofs.CommandGenerators

namespace ComplexityOfGenerators.Simulation.WordStack.BoundedSource

variable {S O : Type} [Fintype S] [Fintype O] (unitSymbol : S) (randomSymbol : Bool → S)

def prepareCommand (seed : PolynomialBound) : Command S O 35 :=
  (Command.loadIndex 13 unitSymbol).seq
  ((counter unitSymbol randomSymbol 18 (by decide) seed).command.seq
  ((Command.collect 18 34 randomSymbol).seq (Command.transfer 34 17 id)))

def preparedMemory (n read : ℕ) (bits : BitString) : Memory (S) O 35 :=
  ⟨(), n, read, [], Function.update
    (Function.update (Function.update (fun _ => []) 13 (List.replicate n unitSymbol))
      19 (List.replicate (n + 1) unitSymbol)) 17 (bits.map randomSymbol)⟩

noncomputable def prepareBudget (seed : PolynomialBound) (n : ℕ) : ℕ :=
  29 * n + 12 * seed n + Command.counterBudget seed n + 12

theorem prepare_runs (seed : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∃ t ≤ prepareBudget seed n,
      (prepareCommand (O := O) unitSymbol randomSymbol seed).Runs n bits Command.emptyMemory t
        (if seed n ≤ bits.length then .done (preparedMemory (O := O) unitSymbol randomSymbol n (seed n) (bits.take (seed n))) else .exhausted) := by
  let loaded : Memory (S) O 35 := Command.loadedIndex 13 unitSymbol n Command.emptyMemory
  let seeded : Memory (S) O 35 := {loaded with store := (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).eval loaded.store}
  have loadRun := Command.loadIndex_runs (13 : Fin 35) (unitSymbol : S) n bits (Command.emptyMemory (O := O)) (Nat.zero_le _)
  have loadIndex : loaded.indexHead ≤ n := le_rfl
  obtain ⟨ticks, tickBound, counterRun⟩ := (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).runs bits loaded loadIndex
  have loadSize : StoreBound loaded.store n := by
    intro j
    simp [loaded, Command.loadedIndex, Command.emptyMemory, Memory.set, Function.update_apply]
    split <;> simp
  have counterCost := CounterRoutine.routine_cost (O := O) (counterSlots 18 (by decide)) seed
    (unitSymbol : S) loaded.store n loadSize
  have count_eq : (seeded.store 18).length = seed n := by
    simp [seeded, loaded, counter, CounterRoutine.routine_eval, Command.loadedIndex, Command.emptyMemory, Memory.set]
  have head_eq : seeded.randomHead = 0 := rfl
  have seededIndex : seeded.indexHead ≤ n := le_rfl
  have size_eq : (loaded.store 13).length = n := by
    simp [loaded, Command.loadedIndex, Command.emptyMemory, Memory.set]
  change (counter (O := O) unitSymbol randomSymbol 18 (by decide) seed).cost loaded.store ≤ _ at counterCost
  simp only [counterSlots_apply, size_eq] at counterCost
  by_cases enough : seed n ≤ bits.length
  · have collectRun := Command.collect_full 18 34 (by decide) (randomSymbol : Bool → S)
      bits seeded seededIndex (by simpa [head_eq, count_eq] using enough)
    let collected := Command.collected 18 34 (randomSymbol : Bool → S) bits seeded (seeded.store 18).length
    have collectedIndex : collected.indexHead ≤ n := le_rfl
    have transferRun := Command.transfer_runs 34 17 (by decide) (id : S → S) bits collected collectedIndex
    have collectedLength : (collected.store 34).length = seed n := by
      simp [collected, Command.collected, seeded, loaded, counter, CounterRoutine.routine_eval,
        Command.loadedIndex, Command.emptyMemory, Memory.set, head_eq, count_eq, Nat.min_eq_left enough]
    have final_eq : (collected.set 34 []).set 17 ((collected.store 34).reverse.map id ++ collected.store 17) =
        preparedMemory (O := O) unitSymbol randomSymbol n (seed n) (bits.take (seed n)) := by
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
  · obtain ⟨t, cost, collectRun⟩ := Command.collect_short 18 34 (by decide) (randomSymbol : Bool → S)
      bits seeded seededIndex (by simp only [head_eq, count_eq]; omega)
    have aborted := Command.Runs.seq_absent seeded (Command.collect 18 34 randomSymbol)
      (Command.transfer 34 17 id) t collectRun
    have seededRun := Command.Runs.seq _ _ _ _ _ _ _ counterRun aborted
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun seededRun
    refine ⟨3 * n + 1 + (ticks + 1 + t), ?_, ?_⟩
    · simp only [count_eq] at cost
      change 3 * (n - 0) + 1 + (ticks + 1 + t) ≤ _
      dsimp only [prepareBudget]
      omega
    · simpa only [prepareCommand, enough, ite_false, Nat.sub_zero] using run

end ComplexityOfGenerators.Simulation.WordStack.BoundedSource
