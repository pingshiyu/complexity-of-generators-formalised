import ComplexityOfGenerators.Simulation.ExactRecursive.Budgets
import ComplexityOfGenerators.Simulation.ExactRecursive.Finish

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def commandValue (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) (n : ℕ) (bits : BitString) :
    Option (List α) :=
  if seed n ≤ bits.length then
    algorithm B V first baseSeed baseTime inverseSeed inverseTime count fuel n (bits.take (seed n)) else none

theorem prepared_bound (n read cap : ℕ) (bits : BitString)
    (index : n + 1 ≤ cap) (random : bits.length ≤ cap) :
    StoreBound (preparedMemory B V n read bits).store cap := by
  have empty : StoreBound (fun (_ : Fin 35) => ([] : List (Cell B V))) cap := by intro j; simp
  exact ((empty.update 13 _ (by simpa using (by omega : n ≤ cap))).update 19 _ (by simpa using index)).update
    17 _ (by simpa using random)

/-- The complete finite command halts on every finite tape. Its accepted value
is the checked sampler on the collected prefix, and short tapes exhaust. -/
theorem command_runs (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) (n cap words : ℕ)
    (budget : BudgetConditions baseSeed baseTime inverseSeed inverseTime count fuel seed n cap words)
    (bits : BitString) :
    ∃ t ≤ prepareBudget seed n + bodyBudget B V baseSeed baseTime inverseSeed inverseTime count fuel n cap +
        4 * cap + bits.length + 4, ∃ result,
      (command B V first baseSeed baseTime inverseSeed inverseTime count fuel seed).Runs n bits Command.emptyMemory t result ∧
        result.outcome.acceptedWord = commandValue B V first baseSeed baseTime inverseSeed inverseTime count fuel seed n bits := by
  obtain ⟨prepareTime, prepareCost, prepareRun⟩ := prepare_runs B V seed n bits
  by_cases full : seed n ≤ bits.length
  · rw [ite_eq_left full] at prepareRun
    let inner := bits.take (seed n)
    let start := preparedMemory B V n (seed n) inner
    let code := body B V first baseSeed baseTime inverseSeed inverseTime count fuel
    have innerLength : inner.length = seed n := by simp [inner, Nat.min_eq_left full]
    have input : start.store 11 = [] := by simp [start, preparedMemory]
    have auxiliary : start.store 12 = [] := by simp [start, preparedMemory]
    have index : (start.store 13).length = n := by simp [start, preparedMemory]
    have random : start.store 17 = inner.map Symbol.bit := by simp [start, preparedMemory]
    have empty : start.store 14 = [] := by simp [start, preparedMemory]
    have stopped : start.store 28 = [] := by simp [start, preparedMemory]
    have enough : baseSeed n + fuel n * (1 + count n * (inverseSeed n + 1)) ≤ inner.length := by
      rw [innerLength]
      exact budget.enough
    obtain ⟨state, rest, stored, target, answer⟩ := body_correct B V first baseSeed baseTime inverseSeed inverseTime
      count fuel n inner start.store input auxiliary index random empty stopped enough
    obtain ⟨storeBound, costBound⟩ := body_bound B V first baseSeed baseTime inverseSeed inverseTime count fuel n
      inner start.store input auxiliary index random empty stopped cap words
      (prepared_bound B V n (seed n) cap inner budget.index (by rw [innerLength]; exact budget.seed_le))
      budget.index budget.baseSeed_le budget.baseTime_le budget.baseWords budget.inverseWords budget.count_le
      budget.inverseSeed_le budget.inverseTime_le budget.fuel_le budget.baseSpace budget.space enough
    obtain ⟨bodyTime, bodyCost, bodyRun⟩ := code.runs bits start (le_refl n)
    let last : Memory (Cell B V) α 35 := {start with store := code.eval start.store}
    obtain ⟨finishTime, finishCost, result, finishRun, value⟩ := finish_runs B V n bits rest last state stored target
      (le_refl n) rfl
    have wordBound : state.word.length ≤ cap := by
      have word := storeBound 11
      rw [stored.input] at word
      simpa [letters] using word
    have restRun := Command.Runs.seq _ _ _ _ _ _ _ bodyRun finishRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ prepareRun restRun
    refine ⟨_, ?_, result, run, ?_⟩
    · change prepareTime + 1 + (bodyTime + 1 + finishTime) ≤ _
      change bodyTime ≤ code.cost start.store at bodyCost
      change code.cost start.store ≤ _ at costBound
      omega
    · rw [commandValue, ite_eq_left full]
      exact value.trans answer
  · rw [ite_eq_right full] at prepareRun
    have run := Command.Runs.seq_absent Command.emptyMemory (prepareCommand B V seed)
      ((body B V first baseSeed baseTime inverseSeed inverseTime count fuel).command.seq (finish B V)) prepareTime prepareRun
    exact ⟨prepareTime, by omega, .exhausted, run, by simp [Result.outcome, Outcome.acceptedWord, commandValue, full]⟩

theorem command_time (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) (n : ℕ)
    (enough : baseSeed n + fuel n * (1 + count n * (inverseSeed n + 1)) ≤ seed n)
    (bits : BitString) (length : bits.length ≤ seed n) :
    ∃ t ≤ stackTime B V baseSeed baseTime inverseSeed inverseTime count fuel seed n, ∃ result,
      (command B V first baseSeed baseTime inverseSeed inverseTime count fuel seed).Runs n bits Command.emptyMemory t result := by
  obtain ⟨t, cost, result, run, _⟩ := command_runs B V first baseSeed baseTime inverseSeed inverseTime count fuel seed n
    _ _ (budgetConditions baseSeed baseTime inverseSeed inverseTime count fuel seed n enough) bits
  refine ⟨t, ?_, result, run⟩
  apply le_trans _ (stackTime_bound B V baseSeed baseTime inverseSeed inverseTime count fuel seed n)
  omega

end ComplexityOfGenerators.Simulation.ExactRecursive
