import ComplexityOfGenerators.Simulation.BalancedPairGenerator.ClassifyBounds
import ComplexityOfGenerators.Simulation.BalancedPairGenerator.Calls
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Components

namespace ComplexityOfGenerators.Simulation.BalancedPairGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem reset_bound (s : Store G) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((reset G).eval s) cap ∧ (reset G).cost s ≤ 30 * cap + 20 := by
  constructor
  · rw [reset_eval]
    exact (((((((((sizes.clear 11).clear 12).clear 14).clear 25).clear 26).clear 27).clear 28).clear 31).clear 32)
  · have a := sizes 11
    have b := sizes 12
    have c := sizes 14
    have d := sizes 25
    have e := sizes 26
    have f := sizes 27
    have g := sizes 28
    have h := sizes 31
    have i := sizes 32
    simp [reset, Routine.seq, Routine.clear, UnionGenerator.flag, Routine.skip, Routine.ofLocal, Local.ticks]
    omega

theorem reset_stored (n : ℕ) (bits : BitString) (s : Store G)
    (index : (s 13).length = n) (random : s 17 = bits.map Symbol.bit) :
    UnionGenerator.Stored G G n bits none none ((reset G).eval s) := by
  constructor <;> simp [reset_eval, index, random, UnionGenerator.held, UnionGenerator.flagWord]

noncomputable def phaseCap (seed time width B : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (100 * (Polynomial.X + 1 + seed.asPolynomial +
    3 * time.asPolynomial + width.asPolynomial + B.asPolynomial))

theorem phaseCap_lower (seed time width B : PolynomialBound) (n : ℕ) :
    100 * (n + 1 + seed n + 3 * time n + width n + B n) ≤ phaseCap seed time width B n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (100 * (Polynomial.X + 1 + seed.asPolynomial + 3 * time.asPolynomial + width.asPolynomial + B.asPolynomial)) n
  simpa only [phaseCap, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_X, PolynomialBound.asPolynomial_eval] using bound

noncomputable def callConstant : ℕ :=
  (Source.body G (Symbol.left : Source.Symbol G → Cell G) (UnionGenerator.leftDecode G G)
    (Source.bank BoundedSource.sourceSlots)).bound +
    (Source.body G (Symbol.right : Source.Symbol G → Cell G) (UnionGenerator.rightDecode G G)
      (Source.bank BoundedSource.sourceSlots)).bound + 1000

noncomputable def callBudget (seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  callConstant G * (cap + 1) + 2 * Command.counterBudget seed n + 2 * Command.counterBudget time n

theorem calls_bound (seed time : PolynomialBound) (n cap : ℕ) (bits : BitString) (s : Store G)
    (sizes : StoreBound s cap) (index : (s 13).length = n) (random : s 17 = bits.map Symbol.bit)
    (base : n + 1 ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap)
    (space : 1 + n + seed n + 3 * (time n + 1) ≤ cap) :
    StoreBound ((calls G seed time).eval s) cap ∧ (calls G seed time).cost s ≤ callBudget G seed time n cap := by
  let initial := (reset G).eval s
  obtain ⟨resetBound, resetCost⟩ := reset_bound G s cap sizes
  have stored := reset_stored G n bits s index random
  change UnionGenerator.Stored G G n bits none none initial at stored
  obtain ⟨leftBound, _, leftCost⟩ := BoundedSource.sourceTrial_bound (O := α) Symbol.unit Symbol.bit G
    Symbol.left (UnionGenerator.leftDecode G G) (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit)
    (UnionGenerator.leftBit G G) (fun _ => rfl) seed time initial (generatorData n) bits
    (by simp [stored.input, generatorData]) (by simp [stored.auxiliary, generatorData])
    stored.index stored.random stored.empty cap resetBound base seedBound timeBound (by simpa [generatorData] using space)
  obtain ⟨leftFinished, leftFinishCost⟩ := UnionGenerator.leftFinish_bound G G _ cap leftBound (by omega)
  have storedLeft := UnionGenerator.leftStep_stored G G seed time n bits none none initial stored
  obtain ⟨rightBound, _, rightCost⟩ := BoundedSource.sourceTrial_bound (O := α) Symbol.unit Symbol.bit G
    Symbol.right (UnionGenerator.rightDecode G G) (fun _ => rfl) (fun _ => .right .unit) (fun _ => .right .unit)
    (UnionGenerator.rightBit G G) (fun _ => rfl) seed time _ (generatorData n) (bits.drop (seed n))
    (by simp [storedLeft.input, generatorData]) (by simp [storedLeft.auxiliary, generatorData])
    storedLeft.index storedLeft.random storedLeft.empty cap leftFinished base seedBound timeBound
    (by simpa [generatorData] using space)
  obtain ⟨rightFinished, rightFinishCost⟩ := UnionGenerator.rightFinish_bound G G _ cap rightBound (by omega)
  refine ⟨rightFinished, ?_⟩
  change (reset G).cost s + 1 + ((UnionGenerator.leftTrial G G seed time).cost initial + 1 +
    ((UnionGenerator.leftFinish G G).cost _ + 1 + ((UnionGenerator.rightTrial G G seed time).cost _ + 1 +
      (UnionGenerator.rightFinish G G).cost _))) ≤ _
  change (UnionGenerator.leftTrial G G seed time).cost initial ≤ _ at leftCost
  change (UnionGenerator.rightTrial G G seed time).cost _ ≤ _ at rightCost
  simp only [generatorData] at leftCost rightCost
  dsimp only [callBudget, callConstant]
  simp only [initial, UnionGenerator.leftTrial, UnionGenerator.rightTrial] at leftCost rightCost leftFinishCost rightFinishCost ⊢
  nlinarith only [resetCost, leftCost, leftFinishCost, rightCost, rightFinishCost]


theorem held_length_le (answer : Option (List α)) (B : ℕ)
    (bound : ∀ word, answer = some word → word.length ≤ B) :
    (UnionGenerator.held G G answer).length ≤ B := by
  cases answer with
  | none => simp [UnionGenerator.held]
  | some word => simpa [UnionGenerator.held, UnionGenerator.letters] using bound word rfl

theorem calls_classifyData (seed time width B : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store G)
    (sizes : StoreBound s (phaseCap seed time width B n))
    (index : (s 13).length = n) (random : s 17 = bits.map Symbol.bit) (length : bits.length = width n)
    (enough : 2 * seed n + B n ≤ width n)
    (short : ∀ block word, BalancedPairPhase.cappedCall G n (time n) block = some word → word.length ≤ B n) :
    ClassifyData G (B n) (width n) (phaseCap seed time width B n) ((calls G seed time).eval s) ∧
      (calls G seed time).cost s ≤ callBudget G seed time n (phaseCap seed time width B n) := by
  have capLower := phaseCap_lower seed time width B n
  have seedPositive := seed.positive n
  have timePositive := time.positive n
  obtain ⟨bounded, cost⟩ := calls_bound G seed time n _ bits s sizes index random
    (by omega) (by omega) (by omega) (by omega)
  have stored := calls_stored G seed time n bits s index random
  refine ⟨⟨bounded, ?_, ?_, ?_, ?_⟩, cost⟩
  · rw [stored.leftWord]
    apply held_length_le
    intro word accepted
    exact short _ _ accepted
  · rw [stored.rightWord]
    apply held_length_le
    intro word accepted
    exact short _ _ accepted
  · rw [stored.random, List.length_map, List.length_drop, length]
    omega
  · rw [stored.random, List.length_map, List.length_drop, length]
    omega

noncomputable def phaseTime (seed time width B : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (Polynomial.C (callConstant G) * ((phaseCap seed time width B).asPolynomial + 1) +
      2 * (Command.counterBudget seed).asPolynomial + 2 * (Command.counterBudget time).asPolynomial + 1 +
      1000000 * ((phaseCap seed time width B).asPolynomial + 1)^2)

theorem phaseTime_lower (seed time width B : PolynomialBound) (n : ℕ) :
    callBudget G seed time n (phaseCap seed time width B n) + 1 +
      1000000 * (phaseCap seed time width B n + 1)^2 ≤ phaseTime G seed time width B n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (Polynomial.C (callConstant G) * ((phaseCap seed time width B).asPolynomial + 1) +
      2 * (Command.counterBudget seed).asPolynomial + 2 * (Command.counterBudget time).asPolynomial + 1 +
      1000000 * ((phaseCap seed time width B).asPolynomial + 1)^2) n
  simpa only [phaseTime, callBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_pow, PolynomialBound.asPolynomial_eval] using bound

/-- A whole bounded balanced-pair phase has one uniform polynomial cap and
clock. Every premise concerns native source runs or its explicit block sizes. -/
theorem phase_bound (seed time width B : PolynomialBound)
    (enough : ∀ n, 2 * seed n + B n ≤ width n)
    (short : ∀ n block word, BalancedPairPhase.cappedCall G n (time n) block = some word → word.length ≤ B n) :
    FixedBlockRetry.PhaseBound Symbol.bit width (phaseCap seed time width B)
      (phaseTime G seed time width B) (phase G seed time) := by
  intro n bits s length index master random sizes
  obtain ⟨data, callsCost⟩ := calls_classifyData G seed time width B n bits s sizes index random length (enough n) (short n)
  have capLower := phaseCap_lower seed time width B n
  obtain ⟨bounded, classifyCost⟩ := classify_bound G (B n) (width n) _ _ data.sizes data.left data.right data.enough data.bits (by omega)
  refine ⟨bounded, ?_⟩
  apply le_trans _ (phaseTime_lower G seed time width B n)
  change (calls G seed time).cost s + 1 + (classify G).cost ((calls G seed time).eval s) ≤ _
  omega

theorem phase_indexBudget (seed time width B : PolynomialBound) (n : ℕ) :
    n + 1 ≤ phaseCap seed time width B n := by
  have := phaseCap_lower seed time width B n
  omega

theorem phase_widthBudget (seed time width B : PolynomialBound) (n : ℕ) :
    width n ≤ phaseCap seed time width B n := by
  have := phaseCap_lower seed time width B n
  omega

end ComplexityOfGenerators.Simulation.BalancedPairGenerator
