import ComplexityOfGenerators.Simulation.StarGenerator.LoopBounds
import ComplexityOfGenerators.Simulation.UnionGenerator.Execution

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

structure BudgetConditions (sourceSeed sourceTime seed : PolynomialBound) (n cap : ℕ) : Prop where
  index : n + 1 ≤ cap
  sourceSeed_le : sourceSeed n ≤ cap
  sourceTime_le : sourceTime n + 1 ≤ cap
  sourceSpace : 1 + n + sourceSeed n + 3 * (sourceTime n + 1) ≤ cap
  wordSpace : n * sourceTime n ≤ cap
  archiveSpace : (n + 1) * (n * sourceTime n + 1) ≤ cap
  seed_le : seed n ≤ cap

noncomputable def storeBudget (sourceSeed sourceTime seed : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (10 * (Polynomial.X + 1 + sourceSeed.asPolynomial + sourceTime.asPolynomial + seed.asPolynomial +
      Polynomial.X * sourceTime.asPolynomial +
      (Polynomial.X + 1) * (Polynomial.X * sourceTime.asPolynomial + 1)))

theorem budgetConditions (sourceSeed sourceTime seed : PolynomialBound) (n : ℕ) :
    BudgetConditions sourceSeed sourceTime seed n (storeBudget sourceSeed sourceTime seed n) := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (10 * (Polynomial.X + 1 + sourceSeed.asPolynomial + sourceTime.asPolynomial + seed.asPolynomial +
      Polynomial.X * sourceTime.asPolynomial +
      (Polynomial.X + 1) * (Polynomial.X * sourceTime.asPolynomial + 1))) n
  change _ ≤ storeBudget sourceSeed sourceTime seed n at bound
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one, PolynomialBound.asPolynomial_eval] at bound
  constructor <;> omega

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

noncomputable def stackTime (sourceSeed sourceTime seed : PolynomialBound) : PolynomialBound :=
  let cap := (storeBudget sourceSeed sourceTime seed).asPolynomial
  let step := Polynomial.C
      ((Source.body G (Symbol.left : Source.Symbol G → Cell G) (UnionGenerator.leftDecode G G)
        (Source.bank BoundedSource.sourceSlots)).bound + 500) * (cap + 1) +
    (Command.counterBudget sourceSeed).asPolynomial + (Command.counterBudget sourceTime).asPolynomial
  let stage := 100 * (cap + 1) + Polynomial.X * (step + 4)
  let body := 30 * (cap + 1) + Polynomial.X * (stage + 4)
  PolynomialBound.ofPolynomial (29 * Polynomial.X + 13 * seed.asPolynomial +
    (Command.counterBudget seed).asPolynomial + body + 4 * cap + 16)

theorem stackTime_bound (sourceSeed sourceTime seed : PolynomialBound) (n : ℕ) :
    let cap := storeBudget sourceSeed sourceTime seed n
    BoundedSource.prepareBudget seed n + bodyBudget G sourceSeed sourceTime n cap +
      4 * cap + seed n + 4 ≤ stackTime G sourceSeed sourceTime seed n := by
  dsimp only [stackTime]
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval,
    BoundedSource.prepareBudget, bodyBudget, stageBudget, stepBudget]
  omega

def commandValue (sourceSeed sourceTime seed : PolynomialBound) (n : ℕ) (bits : BitString) : Option (List α) :=
  if seed n ≤ bits.length then algorithm G sourceSeed sourceTime n (bits.take (seed n)) else none

theorem prepared_bound (n read cap : ℕ) (bits : BitString) (index : n + 1 ≤ cap) (random : bits.length ≤ cap) :
    StoreBound (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store cap :=
  UnionGenerator.prepared_bound G G n read cap bits index random

theorem finish_runs (n : ℕ) (bits : BitString) (m : Memory (Cell G) α 35)
    (answer : Option (List α)) (chosen : Chosen G answer m.store)
    (index : m.indexHead ≤ n) (output : m.output = []) :
    ∃ t ≤ 4 * (m.store 31).length + bits.length + 1, ∃ result,
      (finish G).Runs n bits m t result ∧ result.outcome.acceptedWord = answer := by
  cases answer with
  | none =>
    have run : (finish G).Runs n bits m (1 + (bits.length - m.randomHead)) .exhausted := by
      apply Command.Runs.branch
      simpa [observe, chosen.found, UnionGenerator.flagWord] using Command.Runs.drain (n := n) (bits := bits) m
    exact ⟨_, by omega, _, run, rfl⟩
  | some word =>
    have run : (finish G).Runs n bits m (1 + 4 * (m.store 31).length)
        (.done (Command.emitted 31 (UnionGenerator.outputLetter G G) m)) := by
      apply Command.Runs.branch
      simpa [observe, chosen.found, UnionGenerator.flagWord] using
        Command.emitWord_runs 31 (UnionGenerator.outputLetter G G) bits m index
    refine ⟨_, by omega, _, run, ?_⟩
    simp [Result.outcome, Outcome.acceptedWord, Command.emitted, output, chosen.word,
      UnionGenerator.held, UnionGenerator.letters, List.filterMap_map, Function.comp_def, UnionGenerator.outputLetter]

/-- The actual native command has precisely the finite dynamic-program
semantics. Short collected tapes exhaust; no abstract implementation is assumed. -/
theorem command_runs (sourceSeed sourceTime seed : PolynomialBound) (n cap : ℕ)
    (budget : BudgetConditions sourceSeed sourceTime seed n cap) (bits : BitString) :
    ∃ t ≤ BoundedSource.prepareBudget seed n + bodyBudget G sourceSeed sourceTime n cap +
        4 * cap + bits.length + 4, ∃ result,
      (command G sourceSeed sourceTime seed).Runs n bits Command.emptyMemory t result ∧
        result.outcome.acceptedWord = commandValue G sourceSeed sourceTime seed n bits := by
  obtain ⟨prepareTime, prepareCost, prepareRun⟩ :=
    BoundedSource.prepare_runs (O := α) (Symbol.unit : Cell G) Symbol.bit seed n bits
  by_cases full : seed n ≤ bits.length
  · rw [ite_eq_left full] at prepareRun
    let inner := bits.take (seed n)
    let start := BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n (seed n) inner
    let code := body G sourceSeed sourceTime
    have innerLength : inner.length = seed n := by simp [inner, Nat.min_eq_left full]
    have chosen := body_chosen G sourceSeed sourceTime n (seed n) inner
    obtain ⟨storeBound, costBound⟩ := body_bound G sourceSeed sourceTime n (seed n) cap inner
      (prepared_bound G n (seed n) cap inner budget.index (by rw [innerLength]; exact budget.seed_le))
      budget.index budget.sourceSeed_le budget.sourceTime_le budget.sourceSpace budget.wordSpace budget.archiveSpace
    obtain ⟨bodyTime, bodyCost, bodyRun⟩ := code.runs bits start (le_refl n)
    let last : Memory (Cell G) α 35 := {start with store := code.eval start.store}
    obtain ⟨finishTime, finishCost, result, finishRun, answer⟩ := finish_runs G n bits last _ chosen (le_refl n) rfl
    have wordBound : (last.store 31).length ≤ cap := storeBound 31
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
      ((body G sourceSeed sourceTime).command.seq (finish G)) prepareTime prepareRun
    exact ⟨prepareTime, by omega, .exhausted, run,
      by simp [Result.outcome, Outcome.acceptedWord, commandValue, full]⟩

theorem command_time (sourceSeed sourceTime seed : PolynomialBound) (n : ℕ) (bits : BitString)
    (length : bits.length ≤ seed n) :
    ∃ t ≤ stackTime G sourceSeed sourceTime seed n, ∃ result,
      (command G sourceSeed sourceTime seed).Runs n bits Command.emptyMemory t result := by
  obtain ⟨t, cost, result, run, _⟩ := command_runs G sourceSeed sourceTime seed n _
    (budgetConditions sourceSeed sourceTime seed n) bits
  refine ⟨t, ?_, result, run⟩
  apply le_trans _ (stackTime_bound G sourceSeed sourceTime seed n)
  omega

end ComplexityOfGenerators.Simulation.StarGenerator
