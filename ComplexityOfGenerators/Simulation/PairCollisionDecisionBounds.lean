import ComplexityOfGenerators.Simulation.PairCollisionDecisionCorrectness
import ComplexityOfGenerators.Simulation.WordStack.CounterRandomFree

namespace ComplexityOfGenerators.Simulation.PairCollisionDecision
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (M : Machine Bool Bool Unit)

theorem loaded_bound (word : List PairSymbol) : StoreBound (loaded M word).store word.length := by
  intro j
  by_cases same : j=20 <;>simp [loaded,Function.update_apply,same]

theorem counter_input (p : PolynomialBound) (word : List PairSymbol) :
    (counter M p).eval (loaded M word).store 20=word.reverse.map Cell.pair := by
  simp [counter,CounterRoutine.routine_eval,loaded]

theorem prepared_bound (p : PolynomialBound) (word : List PairSymbol) :
    StoreBound (prepared M p word) (sourceClock p word.length+2*word.length+2) := by
  intro j
  rw [prepared_eq]
  by_cases h11 : j=11 <;>by_cases h16 : j=16 <;>by_cases h23 : j=23 <;>
    simp_all [Function.update_apply,binaryPairWord_length] <;>omega

def callConstant : ℕ := (Source.body M Cell.source (sourceDecode M) (Source.bank sourceSlots)).bound+105

def primitiveBudget (p : PolynomialBound) (n : ℕ) : ℕ :=
  34*n+12+Command.counterBudget (sourceClock p) n+callConstant M*(sourceClock p n+2*n+3)

theorem routine_cost (p : PolynomialBound) (word : List PairSymbol) :
    (routine M p).cost (loaded M word).store+3≤primitiveBudget M p word.length := by
  have counterCost := CounterRoutine.routine_cost (O:=Unit) counterSlots (sourceClock p) (Cell.unit : Cell M)
    (loaded M word).store word.length (loaded_bound M word)
  have inputSize : ((loaded M word).store (counterSlots 0)).length=word.length := by simp [counterSlots,loaded]
  rw [inputSize] at counterCost
  change (counter M p).cost (loaded M word).store≤26*word.length+7+
    Command.counterBudget (sourceClock p) word.length at counterCost
  have expandCost : (expand M).cost ((counter M p).eval (loaded M word).store)=8*word.length := by
    change 8*((counter M p).eval (loaded M word).store 20).length=_
    rw [counter_input]
    simp
  have sourceCost := Source.call_cost (Output:=Unit) M sourceSlots Cell.source (sourceDecode M) id id id
    (prepared M p word) (sourceClock p word.length+2*word.length+2) (prepared_bound M p word)
  change (call M).cost (prepared M p word)≤callConstant M*(sourceClock p word.length+2*word.length+2+1) at sourceCost
  have sameBudget : sourceClock p word.length+2*word.length+2+1=
      sourceClock p word.length+2*word.length+3 := by omega
  rw [sameBudget] at sourceCost
  change (counter M p).cost (loaded M word).store+1+
    (expand M).cost ((counter M p).eval (loaded M word).store)+1+(call M).cost (prepared M p word)+3≤_
  rw [expandCost]
  unfold primitiveBudget
  omega

def primitiveTime (p : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (34*Polynomial.X+12+(Command.counterBudget (sourceClock p)).asPolynomial+
    Polynomial.C (callConstant M)*((sourceClock p).asPolynomial+2*Polynomial.X+3))

theorem primitiveBudget_le (p : PolynomialBound) (n : ℕ) : primitiveBudget M p n≤primitiveTime M p n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp [primitiveBudget,Polynomial.eval_add,Polynomial.eval_mul,PolynomialBound.asPolynomial_eval]

theorem routine_pure (p : PolynomialBound) : Command.RandomFree (routine M p).command := by
  have counterPure : Command.RandomFree (counter M p).command := by
    simp [counter,CounterRoutine.routine,CounterRoutine.setup,Command.polynomialCounter]
  have expanded : Command.RandomFree (expand M).command := PairCollisionExpandTwo.pure 20 11 (first M) (second M)
  have called : Command.RandomFree (call M).command := by
    simp [call,Source.call,Source.prepare]
  exact .seq (.seq counterPure expanded) called

end
end ComplexityOfGenerators.Simulation.PairCollisionDecision
