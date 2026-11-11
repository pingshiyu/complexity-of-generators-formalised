import ComplexityOfGenerators.Simulation.ExpectedCollisionSearchBounds

namespace ComplexityOfGenerators.Simulation.ExpectedCollisionSearch

open WordStack

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable (M : Machine Unit Bool Bool)

def preparedMemory (n read : ℕ) (bits : BitString) : Memory (Cell M) Bool 35 :=
  ⟨(), n, read, [], Function.update
    (Function.update (Function.update (fun _ => []) 24 (List.replicate n Symbol.unit))
      25 (List.replicate (n + 1) Symbol.unit)) 17 (bits.reverse.map Symbol.bit)⟩

def prepareBudget (p : PolynomialBound) (n : ℕ) : ℕ :=
  29 * n + 12 * (p n + 1) + Command.counterBudget p n + 20

def setupBudget (p : PolynomialBound) (n : ℕ) : ℕ :=
  60 * cap p n + Command.counterBudget ⟨4, 1, by decide⟩ n +
    Command.counterBudget ⟨8, 1, by decide⟩ n + 100

/-- The search requests exactly one finite random block.  Short supplied tapes
exhaust during collection, without entering the deterministic search loop. -/
theorem prepare_runs (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∃ t ≤ prepareBudget p n,
      (prepareCommand M p).Runs n bits Command.emptyMemory t
        (if p n + 1 ≤ bits.length then
          .done (preparedMemory M n (p n + 1) (bits.take (p n + 1))) else .exhausted) := by
  let loaded : Memory (Cell M) Bool 35 :=
    Command.loadedIndex 24 Symbol.unit n Command.emptyMemory
  let seeded : Memory (Cell M) Bool 35 :=
    {loaded with store := (counter M 18 (by decide) p).eval loaded.store}
  let pushed := seeded.set 18 (Symbol.unit :: seeded.store 18)
  have loadRun := Command.loadIndex_runs (24 : Fin 35) (Symbol.unit : Cell M)
    n bits (Command.emptyMemory (O := Bool)) (Nat.zero_le _)
  have loadIndex : loaded.indexHead ≤ n := le_rfl
  obtain ⟨ticks, tickBound, counterRun⟩ := (counter M 18 (by decide) p).runs bits loaded loadIndex
  have loadSize : StoreBound loaded.store n := by
    intro j
    simp [loaded, Command.loadedIndex, Memory.set, Function.update_apply]
    split <;> simp
  have counterCost := CounterRoutine.routine_cost (O := Bool) (counterSlots 18 (by decide)) p
    (Symbol.unit : Cell M) loaded.store n loadSize
  have count_eq : (pushed.store 18).length = p n + 1 := by
    simp [pushed, seeded, loaded, counter_eval, Command.loadedIndex, Memory.set]
  have head_eq : pushed.randomHead = 0 := rfl
  have pushedIndex : pushed.indexHead ≤ n := le_rfl
  have size_eq : (loaded.store 24).length = n := by
    simp [loaded, Command.loadedIndex, Memory.set]
  change (counter M 18 (by decide) p).cost loaded.store ≤ _ at counterCost
  simp only [counterSlots_apply, size_eq] at counterCost
  have pushRun := Command.push_runs 18 (Symbol.unit : Cell M) bits seeded loadIndex
  by_cases enough : p n + 1 ≤ bits.length
  · have collectRun := Command.collect_full 18 17 (by decide) (Symbol.bit : Bool → Cell M)
      bits pushed pushedIndex (by simpa [head_eq, count_eq] using enough)
    have final_eq : Command.collected 18 17 (Symbol.bit : Bool → Cell M)
        bits pushed (pushed.store 18).length =
        preparedMemory M n (p n + 1) (bits.take (p n + 1)) := by
      apply Configuration.ext <;> try rfl
      · simp [Command.collected, head_eq, count_eq, preparedMemory]
      · funext j
        fin_cases j <;>
          simp [Command.collected, pushed, seeded, loaded, counter_eval,
            Command.loadedIndex, Memory.set, preparedMemory]
    rw [final_eq, count_eq] at collectRun
    have pushedRun := Command.Runs.seq _ _ _ _ _ _ _ pushRun collectRun
    have seededRun := Command.Runs.seq _ _ _ _ _ _ _ counterRun pushedRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun seededRun
    refine ⟨3 * n + 1 + (ticks + 1 + (1 + 1 + 6 * (p n + 1))), ?_, ?_⟩
    · change 3 * (n - 0) + 1 + (ticks + 1 + (1 + 1 + 6 * (p n + 1))) ≤ _
      simp only [Nat.sub_zero]
      dsimp only [prepareBudget]
      omega
    · simpa only [prepareCommand, enough, ite_true, Nat.sub_zero] using run
  · obtain ⟨t, cost, collectRun⟩ := Command.collect_short 18 17 (by decide)
      (Symbol.bit : Bool → Cell M) bits pushed pushedIndex
      (by simp only [head_eq, count_eq]; omega)
    have pushedRun := Command.Runs.seq _ _ _ _ _ _ _ pushRun collectRun
    have seededRun := Command.Runs.seq _ _ _ _ _ _ _ counterRun pushedRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun seededRun
    refine ⟨3 * n + 1 + (ticks + 1 + (1 + 1 + t)), ?_, ?_⟩
    · simp only [count_eq] at cost
      change 3 * (n - 0) + 1 + (ticks + 1 + (1 + 1 + t)) ≤ _
      simp only [Nat.sub_zero]
      dsimp only [prepareBudget]
      omega
    · simpa only [prepareCommand, enough, ite_false, Nat.sub_zero] using run

def readyStore (n : ℕ) (bits : BitString) : Store M :=
  Function.update (Function.update (preparedMemory M n 0 bits).store
    22 (List.replicate (target n) Symbol.unit))
    23 (List.replicate (trials n) Symbol.unit)

theorem setup_prepared_eval (p : PolynomialBound) (n read : ℕ) (bits : BitString) :
    (setup M p).eval (preparedMemory M n read bits).store = readyStore M n bits := by
  funext j
  fin_cases j <;>
    simp [setup, targetCounter, trialsCounter, WordStack.Routine.seq,
      WordStack.Routine.ofLocal, Local.eval_push, counter_eval, preparedMemory,
      readyStore, PolynomialBound.eval, target, trials, List.replicate_succ]
  simp only [← List.replicate_succ]
  congr 1
  omega

theorem setup_prepared_stored (p : PolynomialBound) (n read : ℕ) (bits : BitString) :
    Stored M n 0 bits [] ((setup M p).eval (preparedMemory M n read bits).store) ∧
      (((setup M p).eval (preparedMemory M n read bits).store) 23).length = trials n := by
  rw [setup_prepared_eval]
  constructor
  · constructor <;> simp [readyStore, preparedMemory]
  · simp [readyStore]

theorem prepared_bound (p : PolynomialBound) (n read : ℕ) (bits : BitString)
    (seed : bits.length ≤ p n + 1) :
    StoreBound (preparedMemory M n read bits).store (cap p n) := by
  have empty : StoreBound (fun (_ : Fin 35) => ([] : List (Cell M))) (cap p n) := by
    intro j
    simp
  apply ((empty.update 24 _ (by simp [cap]; omega)).update 25 _ (by simp [cap]; omega)).update
    17 _ (by simpa using seed.trans (by simp [cap]; omega))

theorem ready_bound (p : PolynomialBound) (n : ℕ) (bits : BitString)
    (seed : bits.length ≤ p n + 1) : StoreBound (readyStore M n bits) (cap p n) := by
  exact ((prepared_bound M p n 0 bits seed).update 22 _
    (by simp [target, cap]; omega)).update 23 _ (by simp [trials, target, cap]; omega)

theorem setup_prepared_cost (p : PolynomialBound) (n read : ℕ) (bits : BitString)
    (seed : bits.length ≤ p n + 1) :
    (setup M p).cost (preparedMemory M n read bits).store ≤ setupBudget p n := by
  let s := (preparedMemory M n read bits).store
  let a := (targetCounter M).eval s
  let q₄ : PolynomialBound := ⟨4, 1, by decide⟩
  let q₈ : PolynomialBound := ⟨8, 1, by decide⟩
  let c := (counter M 22 (by decide) q₄).eval s
  have sizes : StoreBound s (cap p n) := prepared_bound M p n read bits seed
  have physical : (s 24).length = n := by simp [s, preparedMemory]
  obtain ⟨cBound, cCost⟩ := counter_bound M 22 (by decide) q₄ s n (cap p n) sizes physical
    (by simp [cap]; omega) (by simp [q₄, PolynomialBound.eval, cap]; omega)
  have aBound : StoreBound a (cap p n) := by
    have updated := cBound.update 22 (Symbol.unit :: Symbol.unit :: c 22)
      (by simp [c, counter_eval, physical, q₄, PolynomialBound.eval, cap]; omega)
    simpa [a, c, q₄, targetCounter, WordStack.Routine.seq, WordStack.Routine.ofLocal,
      Local.eval_push, Function.update_idem] using updated
  have aPhysical : (a 24).length = n := by
    simp [a, targetCounter, WordStack.Routine.seq, WordStack.Routine.ofLocal,
      Local.eval_push, counter_eval, physical]
  obtain ⟨_, dCost⟩ := counter_bound M 23 (by decide) q₈ a n (cap p n) aBound aPhysical
    (by simp [cap]; omega) (by simp [q₈, PolynomialBound.eval, cap]; omega)
  have firstCost : (targetCounter M).cost s = (counter M 22 (by decide) q₄).cost s + 4 := by
    simp [targetCounter, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.push, Local.ticks, q₄]
  have secondCost : (trialsCounter M).cost a = (counter M 23 (by decide) q₈).cost a + 10 := by
    simp [trialsCounter, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.push, Local.ticks, q₈]
  change (targetCounter M).cost s + 1 + (trialsCounter M).cost a ≤ _
  rw [firstCost, secondCost]
  dsimp only [setupBudget, q₄, q₈] at *
  omega

def commandBudget (p : PolynomialBound) (n : ℕ) : ℕ :=
  prepareBudget p n + setupBudget p n + searchBudget M p n + 4 * cap p n + 10

/-- The finite search halts within one polynomial stack-instruction budget on
every finite random tape.  Tapes shorter than the collected block exhaust;
otherwise the exact output is the deterministic bounded-index search result. -/
theorem command_runs (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∃ t ≤ commandBudget M p n, ∃ result,
      (command M p).Runs n bits Command.emptyMemory t result ∧
        result.outcome = if p n + 1 ≤ bits.length then
          .accepted (foldAnswer M p n (bits.take (p n + 1)) 0 (trials n) []) else .exhausted := by
  obtain ⟨prepareTime, prepareCost, prepareRun⟩ := prepare_runs M p n bits
  by_cases enough : p n + 1 ≤ bits.length
  · rw [ite_eq_left enough] at prepareRun
    let inner := bits.take (p n + 1)
    let start := preparedMemory M n (p n + 1) inner
    let code := (setup M p).seq (search M p)
    have innerLength : inner.length ≤ p n + 1 := by simp [inner]
    obtain ⟨stored, count⟩ := setup_prepared_stored M p n (p n + 1) inner
    have setupSize : StoreBound ((setup M p).eval start.store) (cap p n) := by
      rw [show start.store = (preparedMemory M n (p n + 1) inner).store from rfl,
        setup_prepared_eval]
      exact ready_bound M p n inner innerLength
    obtain ⟨finalSize, searchCost⟩ := search_bound M p n inner
      ((setup M p).eval start.store) stored setupSize count innerLength
    have setupCost := setup_prepared_cost M p n (p n + 1) inner innerLength
    obtain ⟨bodyTime, bodyCost, bodyRun⟩ := code.runs bits start (le_refl n)
    let last : Memory (Cell M) Bool 35 := {start with store := code.eval start.store}
    have outputBound : (last.store 34).length ≤ cap p n := finalSize 34
    have saved : last.store 34 = (foldAnswer M p n inner 0 (trials n) []).map Symbol.bit := by
      change (search M p).eval ((setup M p).eval start.store) 34 = _
      exact search_saved M p n inner ((setup M p).eval start.store) stored count
    have finishRun := Command.emitWord_runs 34 (decodeBit M) bits last (le_refl n)
    have emitted : (Command.emitted 34 (decodeBit M) last).output =
        foldAnswer M p n inner 0 (trials n) [] := by
      change last.output ++ (last.store 34).filterMap (decodeBit M) = _
      rw [saved]
      change [] ++ ((foldAnswer M p n inner 0 (trials n) []).map Symbol.bit).filterMap (decodeBit M) = _
      simp [List.filterMap_map, decodeBit]
    have bodyFinish := Command.Runs.seq _ _ _ _ _ _ _ bodyRun finishRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ prepareRun bodyFinish
    refine ⟨prepareTime + 1 + (bodyTime + 1 + 4 * (last.store 34).length), ?_,
      .done (Command.emitted 34 (decodeBit M) last), ?_, ?_⟩
    · change bodyTime ≤ (setup M p).cost start.store + 1 +
        (search M p).cost ((setup M p).eval start.store) at bodyCost
      dsimp only [commandBudget]
      change (setup M p).cost start.store ≤ setupBudget p n at setupCost
      omega
    · exact run
    · simp only [enough, ite_true, WordStack.Result.outcome, emitted, inner]
  · rw [ite_eq_right enough] at prepareRun
    have run := Command.Runs.seq_absent Command.emptyMemory (prepareCommand M p)
      (((setup M p).seq (search M p)).command.seq (Command.emitWord 34 (decodeBit M)))
      prepareTime prepareRun
    refine ⟨prepareTime, ?_, .exhausted, run, ?_⟩
    · dsimp only [commandBudget]
      omega
    · simp only [enough, ite_false, WordStack.Result.outcome]

end
end ComplexityOfGenerators.Simulation.ExpectedCollisionSearch
