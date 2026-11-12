import ComplexityOfGenerators.Simulation.UnionGenerator.Bounds

set_option maxHeartbeats 1600000

namespace ComplexityOfGenerators.Simulation.UnionGenerator

open WordStack

structure BudgetConditions (leftSeed leftTime rightSeed rightTime seed : PolynomialBound)
    (n cap : ℕ) : Prop where
  index : n + 1 ≤ cap
  leftSeed_le : leftSeed n ≤ cap
  leftTime_le : leftTime n + 1 ≤ cap
  rightSeed_le : rightSeed n ≤ cap
  rightTime_le : rightTime n + 1 ≤ cap
  leftSpace : 1 + n + leftSeed n + 3 * (leftTime n + 1) ≤ cap
  rightSpace : 1 + n + rightSeed n + 3 * (rightTime n + 1) ≤ cap
  seed_le : seed n ≤ cap

noncomputable def storeBudget (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) :
    PolynomialBound := PolynomialBound.ofPolynomial
  (10 * (Polynomial.X + 1 + leftSeed.asPolynomial + leftTime.asPolynomial +
    rightSeed.asPolynomial + rightTime.asPolynomial + seed.asPolynomial))

theorem budgetConditions (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) (n : ℕ) :
    BudgetConditions leftSeed leftTime rightSeed rightTime seed n
      (storeBudget leftSeed leftTime rightSeed rightTime seed n) := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (10 * (Polynomial.X + 1 + leftSeed.asPolynomial + leftTime.asPolynomial +
      rightSeed.asPolynomial + rightTime.asPolynomial + seed.asPolynomial)) n
  change _ ≤ storeBudget leftSeed leftTime rightSeed rightTime seed n at bound
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one, PolynomialBound.asPolynomial_eval] at bound
  constructor <;> omega

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

noncomputable def stackTime (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) : PolynomialBound :=
  let cap := (storeBudget leftSeed leftTime rightSeed rightTime seed).asPolynomial
  let body := Polynomial.C
      ((Source.body G (Symbol.left : Source.Symbol G → Cell G H) (leftDecode G H)
        (Source.bank BoundedSource.sourceSlots)).bound +
       (Source.body H (Symbol.right : Source.Symbol H → Cell G H) (rightDecode G H)
        (Source.bank BoundedSource.sourceSlots)).bound + 500) * (cap + 1) +
    (Command.counterBudget leftSeed).asPolynomial + (Command.counterBudget leftTime).asPolynomial +
    (Command.counterBudget rightSeed).asPolynomial + (Command.counterBudget rightTime).asPolynomial
  PolynomialBound.ofPolynomial (29 * Polynomial.X + 13 * seed.asPolynomial +
    (Command.counterBudget seed).asPolynomial + body + 4 * cap + 16)

theorem stackTime_bound (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) (n : ℕ) :
    let cap := storeBudget leftSeed leftTime rightSeed rightTime seed n
    BoundedSource.prepareBudget seed n + bodyBudget G H leftSeed leftTime rightSeed rightTime n cap +
      4 * cap + seed n + 4 ≤ stackTime G H leftSeed leftTime rightSeed rightTime seed n := by
  dsimp only [stackTime]
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval,
    BoundedSource.prepareBudget, bodyBudget]
  omega

/-- Short collected prefixes exhaust before either source is entered. -/
def commandValue (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) (n : ℕ) (bits : BitString) :
    Option (List α) :=
  if seed n ≤ bits.length then value G H leftSeed leftTime rightSeed rightTime n (bits.take (seed n)) else none

theorem prepared_bound (n read cap : ℕ) (bits : BitString)
    (index : n + 1 ≤ cap) (random : bits.length ≤ cap) :
    StoreBound (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store cap := by
  have empty : StoreBound (fun (_ : Fin 35) => ([] : List (Cell G H))) cap := by intro j; simp
  exact ((empty.update 13 _ (by simpa using (by omega : n ≤ cap))).update 19 _
    (by simpa using index)).update 17 _ (by simpa using random)

theorem finish_runs (n : ℕ) (bits : BitString) (m : Memory (Cell G H) α 35)
    (answer : Option (List α)) (chosen : Chosen G H n answer m.store)
    (index : m.indexHead ≤ n) (output : m.output = []) :
    ∃ t ≤ 4 * (m.store 11).length + bits.length + 1, ∃ result,
      (finish G H).Runs n bits m t result ∧ result.outcome.acceptedWord = answer := by
  cases answer with
  | none =>
    have run : (finish G H).Runs n bits m (1 + (bits.length - m.randomHead)) .exhausted := by
      apply Command.Runs.branch
      simpa [observe, chosen.available, flagWord] using Command.Runs.drain (n := n) (bits := bits) m
    exact ⟨_, by omega, _, run, rfl⟩
  | some word =>
    have run : (finish G H).Runs n bits m (1 + 4 * (m.store 11).length)
        (.done (Command.emitted 11 (outputLetter G H) m)) := by
      apply Command.Runs.branch
      simpa [observe, chosen.available, flagWord] using Command.emitWord_runs 11 (outputLetter G H) bits m index
    refine ⟨_, by omega, _, run, ?_⟩
    simp [Result.outcome, Outcome.acceptedWord, Command.emitted, output, chosen.word,
      held, letters, List.filterMap_map, Function.comp_def, outputLetter]

/-- The complete command has the claimed finite-seed semantics, including
empty slices, failed calls, and short random tapes. -/
theorem command_runs (leftSeed leftTime rightSeed rightTime seed : PolynomialBound)
    (n cap : ℕ) (budget : BudgetConditions leftSeed leftTime rightSeed rightTime seed n cap)
    (bits : BitString) :
    ∃ t ≤ BoundedSource.prepareBudget seed n +
        bodyBudget G H leftSeed leftTime rightSeed rightTime n cap + 4 * cap + bits.length + 4,
      ∃ result, (command G H leftSeed leftTime rightSeed rightTime seed).Runs n bits Command.emptyMemory t result ∧
        result.outcome.acceptedWord = commandValue G H leftSeed leftTime rightSeed rightTime seed n bits := by
  obtain ⟨prepareTime, prepareCost, prepareRun⟩ :=
    BoundedSource.prepare_runs (O := α) (Symbol.unit : Cell G H) Symbol.bit seed n bits
  by_cases full : seed n ≤ bits.length
  · rw [ite_eq_left full] at prepareRun
    let inner := bits.take (seed n)
    let start := BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n (seed n) inner
    let code := body G H leftSeed leftTime rightSeed rightTime
    have innerLength : inner.length = seed n := by simp [inner, Nat.min_eq_left full]
    have chosen := body_chosen G H leftSeed leftTime rightSeed rightTime n (seed n) inner
    obtain ⟨storeBound, costBound⟩ := body_bound G H leftSeed leftTime rightSeed rightTime n (seed n) cap inner
      (prepared_bound G H n (seed n) cap inner budget.index (by rw [innerLength]; exact budget.seed_le))
      budget.index budget.leftSeed_le budget.leftTime_le budget.rightSeed_le budget.rightTime_le budget.leftSpace budget.rightSpace
    obtain ⟨bodyTime, bodyCost, bodyRun⟩ := code.runs bits start (le_refl n)
    let last : Memory (Cell G H) α 35 := {start with store := code.eval start.store}
    obtain ⟨finishTime, finishCost, result, finishRun, answer⟩ :=
      finish_runs G H n bits last _ chosen (le_refl n) rfl
    have wordBound : (last.store 11).length ≤ cap := storeBound 11
    have restRun := Command.Runs.seq _ _ _ _ _ _ _ bodyRun finishRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ prepareRun restRun
    refine ⟨_, ?_, result, run, ?_⟩
    · change prepareTime + 1 + (bodyTime + 1 + finishTime) ≤ _
      change bodyTime ≤ code.cost start.store at bodyCost
      change code.cost start.store ≤ _ at costBound
      omega
    · rw [commandValue, ite_eq_left full]
      exact answer
  · rw [ite_eq_right full] at prepareRun
    have run := Command.Runs.seq_absent Command.emptyMemory
      (BoundedSource.prepareCommand Symbol.unit Symbol.bit seed)
      ((body G H leftSeed leftTime rightSeed rightTime).command.seq (finish G H)) prepareTime prepareRun
    exact ⟨prepareTime, by omega, .exhausted, run,
      by simp [Result.outcome, Outcome.acceptedWord, commandValue, full]⟩

theorem command_time (leftSeed leftTime rightSeed rightTime seed : PolynomialBound)
    (n : ℕ) (bits : BitString) (length : bits.length ≤ seed n) :
    ∃ t ≤ stackTime G H leftSeed leftTime rightSeed rightTime seed n, ∃ result,
      (command G H leftSeed leftTime rightSeed rightTime seed).Runs n bits Command.emptyMemory t result := by
  obtain ⟨t, cost, result, run, _⟩ := command_runs G H leftSeed leftTime rightSeed rightTime seed n _
    (budgetConditions leftSeed leftTime rightSeed rightTime seed n) bits
  refine ⟨t, ?_, result, run⟩
  apply le_trans _ (stackTime_bound G H leftSeed leftTime rightSeed rightTime seed n)
  omega

end ComplexityOfGenerators.Simulation.UnionGenerator
