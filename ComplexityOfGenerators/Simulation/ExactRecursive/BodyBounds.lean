import ComplexityOfGenerators.Simulation.ExactRecursive.WalkLoopBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.Body

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem baseFinish_bound (s : Store B V) (cap words : ℕ) (sizes : StoreBound s cap)
    (positive : 1 ≤ cap) (current : (s 11).length ≤ words) (output : (s 10).length ≤ words) :
    StoreBound ((baseFinish B V).eval s) cap ∧
      ((baseFinish B V).eval s 11).length ≤ words ∧
      (baseFinish B V).cost s ≤ 12 * cap + 6 := by
  simp only [baseFinish, WordStack.Routine.branch]
  split
  · obtain ⟨taken, takenCost⟩ := takeOutput_bound B V 11 (by decide) (baseOutput B V) s cap sizes
    obtain ⟨flagged, flagCost⟩ := flag_bound B V 29 true _ cap taken positive
    refine ⟨flagged, ?_, ?_⟩
    · simpa [WordStack.Routine.seq, flag_eval, takeOutput_eval] using output
    · change 1 + ((takeOutput B V 11 (by decide) (baseOutput B V)).cost s + 1 + _) ≤ _
      omega
  · obtain ⟨flagged, flagCost⟩ := flag_bound B V 29 false s cap sizes positive
    exact ⟨flagged, by simpa [flag_eval] using current, by omega⟩

noncomputable def bodyBudget (baseSeed baseTime inverseSeed inverseTime count fuel : PolynomialBound)
    (n cap : ℕ) : ℕ :=
  ((Source.body B (Symbol.base : Source.Symbol B → Cell B V) (baseDecode B V)
    (Source.bank sourceSlots)).bound + 400) * (cap + 1) +
      Command.counterBudget baseSeed n + Command.counterBudget baseTime n + Command.counterBudget fuel n +
        fuel n * (walkStepBudget B V count inverseSeed inverseTime n cap + 4)

theorem body_bound (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel : PolynomialBound) (n : ℕ)
    (bits : BitString) (s : Store B V)
    (input : s 11 = []) (auxiliary : s 12 = []) (index : (s 13).length = n)
    (random : s 17 = bits.map Symbol.bit) (empty : s 14 = []) (stopped : s 28 = [])
    (cap words : ℕ) (sizes : StoreBound s cap) (indexBound : n + 1 ≤ cap)
    (baseSeedBound : baseSeed n ≤ cap) (baseTimeBound : baseTime n + 1 ≤ cap)
    (baseWords : baseTime n + 1 ≤ words) (inverseWords : inverseTime n + 1 ≤ words)
    (countBound : count n ≤ cap) (seedBound : inverseSeed n ≤ cap) (timeBound : inverseTime n + 1 ≤ cap)
    (fuelBound : fuel n ≤ cap)
    (baseSpace : 1 + n + baseSeed n + 3 * (baseTime n + 1) ≤ cap)
    (space : 1 + words + count n + n + inverseSeed n + 3 * (inverseTime n + 1) ≤ cap)
    (enough : baseSeed n + fuel n * (1 + count n * (inverseSeed n + 1)) ≤ bits.length) :
    StoreBound ((body B V first baseSeed baseTime inverseSeed inverseTime count fuel).eval s) cap ∧
      (body B V first baseSeed baseTime inverseSeed inverseTime count fuel).cost s ≤
        bodyBudget B V baseSeed baseTime inverseSeed inverseTime count fuel n cap := by
  let trial := (baseTrial B V baseSeed baseTime).eval s
  let start := (baseFinish B V).eval trial
  let initial := baseState (baseValue B baseTime n (bits.take (baseSeed n)))
  obtain ⟨trialSize, trialOutput, trialCost⟩ := sourceTrial_bound B V B Symbol.base (baseDecode B V)
    (fun _ => rfl) (fun _ => .base .unit) (fun _ => .base .unit) (baseBit B V) (fun _ => rfl)
    baseSeed baseTime s (generatorData n) bits (by simp [input, generatorData]) (by simp [auxiliary, generatorData])
    index random empty cap sizes indexBound baseSeedBound baseTimeBound (by simpa [generatorData] using baseSpace)
  have trialWord : trial 11 = [] := by
    simpa [trial, baseTrial, trialPrepared, input] using sourceTrial_outside B V B Symbol.base (baseDecode B V)
      (fun _ => .base .unit) (fun _ => .base .unit) (baseBit B V) baseSeed baseTime s 11 (by decide) (by decide)
  obtain ⟨startSize, startWord, startCost⟩ := baseFinish_bound B V trial cap words trialSize (by omega)
    (by simp [trialWord]) (trialOutput.trans baseWords)
  have base := baseTrial_view B V baseSeed baseTime n bits s input auxiliary index random empty stopped
  change WalkStored B V n initial (bits.drop (baseSeed n)) start at base
  let counted := (counter B V 22 (by decide) fuel).eval start
  have clocked : WalkStored B V n initial (bits.drop (baseSeed n)) counted := by
    rcases base with ⟨hi, hn, hr, he, hv, hs⟩
    constructor <;> simp_all [counted, counter, CounterRoutine.routine_eval]
  have count_eq : (counted 22).length = fuel n := by
    simp [counted, counter, CounterRoutine.routine_eval, base.index]
  obtain ⟨counterSize, counterCost⟩ := counter_bound B V 22 (by decide) fuel start n cap startSize base.index indexBound fuelBound
  have remaining : fuel n * (1 + count n * (inverseSeed n + 1)) ≤ (bits.drop (baseSeed n)).length := by
    simp only [List.length_drop]
    omega
  have initialSize : initial.word.length ≤ words := by
    change (start 11).length ≤ words at startWord
    simpa [base.input, letters] using startWord
  obtain ⟨loopSize, loopWord, loopCost⟩ := walkIter_bound B V first count inverseSeed inverseTime n (fuel n)
    (initial, bits.drop (baseSeed n)) counted clocked cap words counterSize indexBound countBound seedBound timeBound
    inverseWords initialSize space remaining
  let code := WordStack.Routine.counted 22 (walkStep B V first count inverseSeed inverseTime)
  let finalStore := code.eval^[fuel n] counted
  have finalSize := loopSize.lengthTest (O := α) lengthSlots Symbol.unit (by omega : 1 ≤ cap)
  have finalCost := LengthTest.routine_cost (O := α) lengthSlots (Symbol.unit : Cell B V) finalStore cap loopSize
  constructor
  · change StoreBound ((lengthTest B V).eval (code.eval^[(counted 22).length] counted)) cap
    rw [count_eq]
    exact finalSize
  · change (baseTrial B V baseSeed baseTime).cost s + 1 +
      ((baseFinish B V).cost trial + 1 + ((counter B V 22 (by decide) fuel).cost start + 1 +
      (WordStack.Routine.loopCost code.cost code.eval (counted 22).length counted + 1 +
      (lengthTest B V).cost (code.eval^[(counted 22).length] counted)))) ≤ _
    rw [count_eq]
    change (baseTrial B V baseSeed baseTime).cost s ≤ _ at trialCost
    change (lengthTest B V).cost finalStore ≤ 80 * (cap + 1) at finalCost
    dsimp only [bodyBudget, code, finalStore, generatorData] at trialCost loopCost finalCost ⊢
    nlinarith

end ComplexityOfGenerators.Simulation.ExactRecursive
