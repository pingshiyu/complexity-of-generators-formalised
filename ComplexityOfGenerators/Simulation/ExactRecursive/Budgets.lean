import ComplexityOfGenerators.Simulation.ExactRecursive.BodyBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.Prepare

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

structure BudgetConditions (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound)
    (n cap words : ℕ) : Prop where
  index : n + 1 ≤ cap
  baseSeed_le : baseSeed n ≤ cap
  baseTime_le : baseTime n + 1 ≤ cap
  baseWords : baseTime n + 1 ≤ words
  inverseWords : inverseTime n + 1 ≤ words
  count_le : count n ≤ cap
  inverseSeed_le : inverseSeed n ≤ cap
  inverseTime_le : inverseTime n + 1 ≤ cap
  fuel_le : fuel n ≤ cap
  baseSpace : 1 + n + baseSeed n + 3 * (baseTime n + 1) ≤ cap
  space : 1 + words + count n + n + inverseSeed n + 3 * (inverseTime n + 1) ≤ cap
  seed_le : seed n ≤ cap
  enough : baseSeed n + fuel n * (1 + count n * (inverseSeed n + 1)) ≤ seed n

noncomputable def storeBudget (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) :
    PolynomialBound := PolynomialBound.ofPolynomial
  (10 * (Polynomial.X + 1 + baseSeed.asPolynomial + baseTime.asPolynomial + inverseSeed.asPolynomial +
    inverseTime.asPolynomial + count.asPolynomial + fuel.asPolynomial + seed.asPolynomial))

theorem budgetConditions (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) (n : ℕ)
    (enough : baseSeed n + fuel n * (1 + count n * (inverseSeed n + 1)) ≤ seed n) :
    BudgetConditions baseSeed baseTime inverseSeed inverseTime count fuel seed n
      (storeBudget baseSeed baseTime inverseSeed inverseTime count fuel seed n) (baseTime n + inverseTime n + 1) := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (10 * (Polynomial.X + 1 + baseSeed.asPolynomial + baseTime.asPolynomial + inverseSeed.asPolynomial +
      inverseTime.asPolynomial + count.asPolynomial + fuel.asPolynomial + seed.asPolynomial)) n
  change _ ≤ storeBudget baseSeed baseTime inverseSeed inverseTime count fuel seed n at bound
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one, PolynomialBound.asPolynomial_eval] at bound
  constructor <;> omega

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def stackTime (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) :
    PolynomialBound :=
  let cap := (storeBudget baseSeed baseTime inverseSeed inverseTime count fuel seed).asPolynomial
  let step := Polynomial.C ((Source.body V (Symbol.inverse : Source.Symbol V → Cell B V)
    (inverseDecode B V) (Source.bank sourceSlots)).bound + 250) * (cap + 1) +
      (Command.counterBudget inverseSeed).asPolynomial + (Command.counterBudget inverseTime).asPolynomial
  let search := 70 * cap + 40 + (Command.counterBudget count).asPolynomial + count.asPolynomial * (step + 4)
  let walk := 100 * (cap + 1) + search
  let body := Polynomial.C ((Source.body B (Symbol.base : Source.Symbol B → Cell B V)
    (baseDecode B V) (Source.bank sourceSlots)).bound + 400) * (cap + 1) +
      (Command.counterBudget baseSeed).asPolynomial + (Command.counterBudget baseTime).asPolynomial +
      (Command.counterBudget fuel).asPolynomial + fuel.asPolynomial * (walk + 4)
  PolynomialBound.ofPolynomial (29 * Polynomial.X + 13 * seed.asPolynomial +
    (Command.counterBudget seed).asPolynomial + body + 4 * cap + 16)

theorem stackTime_bound (baseSeed baseTime inverseSeed inverseTime count fuel seed : PolynomialBound) (n : ℕ) :
    let cap := storeBudget baseSeed baseTime inverseSeed inverseTime count fuel seed n
    prepareBudget seed n + bodyBudget B V baseSeed baseTime inverseSeed inverseTime count fuel n cap +
      4 * cap + seed n + 4 ≤ stackTime B V baseSeed baseTime inverseSeed inverseTime count fuel seed n := by
  dsimp only [stackTime]
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval,
    prepareBudget, bodyBudget, walkStepBudget, searchBudget, searchStepBudget]
  omega

end ComplexityOfGenerators.Simulation.ExactRecursive
