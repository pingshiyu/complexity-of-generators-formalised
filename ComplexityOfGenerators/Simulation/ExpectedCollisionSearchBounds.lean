import ComplexityOfGenerators.Simulation.ExpectedCollisionSearch

namespace ComplexityOfGenerators.Simulation.ExpectedCollisionSearch

open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Unit Bool Bool)

def cap (p : PolynomialBound) (n : ℕ) : ℕ := 100 * (n + p n + 1)

def trialBudget (p : PolynomialBound) (n : ℕ) : ℕ :=
  ((Source.body M Symbol.source (sourceDecode M) (Source.bank sourceSlots)).bound + 500) *
    (cap p n + 1) + Command.counterBudget p n

theorem counter_bound (dst : Fin 35) (different) (p : PolynomialBound)
    (s : Store M) (n budget : ℕ) (sizes : StoreBound s budget) (physical : (s 24).length = n)
    (base : n + 1 ≤ budget) (result : p n ≤ budget) :
    StoreBound ((counter M dst different p).eval s) budget ∧
      (counter M dst different p).cost s ≤ 26 * budget + 7 + Command.counterBudget p n := by
  constructor
  · apply sizes.counter (counterSlots dst different) p .unit
    · simpa [physical] using base
    · simpa [physical] using result
  · simpa [counter, physical] using CounterRoutine.routine_cost (O := Bool)
      (counterSlots dst different) p (Symbol.unit : Cell M) s budget sizes

theorem trialSetup_bound (p : PolynomialBound) (n : ℕ) (s : Store M)
    (sizes : StoreBound s (cap p n)) (physical : (s 24).length = n) :
    StoreBound ((trialSetup M p).eval s) (cap p n) ∧
      (trialSetup M p).cost s ≤ 46 * cap p n + 20 + Command.counterBudget p n := by
  let a := (WordStack.Routine.assign (O := Bool) 17 14 18 (by decide) (by decide) (by decide) id).eval s
  let b := (counter M 16 (by decide) p).eval a
  have aBound := sizes.assign (O := Bool) 17 14 18 (by decide) (by decide) (by decide) id
  have aPhysical : (a 24).length = n := by simpa [a] using physical
  obtain ⟨bBound, bCost⟩ := counter_bound M 16 (by decide) p a n (cap p n) aBound aPhysical
    (by simp [cap]; omega) (by simp [cap]; omega)
  have clock : (b 16).length = p n := by simp [b, counter_eval, aPhysical]
  constructor
  · change StoreBound (Function.update b 16 (.unit :: b 16)) _
    exact bBound.update 16 _ (by simp [clock, cap]; omega)
  · have h14 := sizes 14
    have h17 := sizes 17
    have h18 := sizes 18
    change (WordStack.Routine.assign (O := Bool) 17 14 18 (by decide) (by decide) (by decide) id).cost s + 1 +
      ((counter M 16 (by decide) p).cost a + 1 + 1) ≤ _
    rw [WordStack.Routine.assign_cost]
    omega

theorem sourceTrial_bound (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) (s : Store M)
    (h : Stored M n j bits answer s) (sizes : StoreBound s (cap p n))
    (index : j ≤ 2 * target n) (seed : bits.length ≤ p n + 1) :
    StoreBound ((sourceTrial M p).eval s) (cap p n) ∧
      (sourceTrial M p).cost s ≤
        ((Source.body M Symbol.source (sourceDecode M) (Source.bank sourceSlots)).bound + 200) *
          (cap p n + 1) + Command.counterBudget p n := by
  let prepared := (trialSetup M p).eval s
  obtain ⟨setupBound, setupCost⟩ := trialSetup_bound M p n s sizes h.physical
  have iEq : (prepared (sourceSlots 11)).map (fun _ => (Symbol.source .unit : Cell M)) =
      (generatorData j).input.map (fun a => Symbol.source (Source.Cell.input a)) := by
    simp [prepared, trialSetup_eval, h.input, generatorData]
  have aEq : (prepared (sourceSlots 12)).map (fun _ => (Symbol.source .unit : Cell M)) =
      (generatorData j).auxiliary.map (fun a => Symbol.source (Source.Cell.auxiliary a)) := by
    simp [prepared, trialSetup_eval, h.auxiliary, generatorData]
  have nEq : (prepared (sourceSlots 13)).length = (generatorData j).index := by
    simpa [prepared, trialSetup_eval, generatorData] using h.index
  have rEq : (prepared (sourceSlots 14)).reverse.map (sourceBit M) =
      bits.map (fun a => Symbol.source (Source.Cell.bit a)) := by
    simp [prepared, trialSetup_eval, h.random, List.map_reverse, List.map_map, Function.comp_def, sourceBit]
  have clock : (prepared (sourceSlots 16)).length = p n + 1 := by
    simp [prepared, trialSetup_eval, h.physical]
  constructor
  · change StoreBound ((sourceCall M).eval prepared) _
    apply Source.call_size_of_bound M sourceSlots Symbol.source (sourceDecode M) (fun _ => rfl)
      (fun _ => .source .unit) (fun _ => .source .unit) (sourceBit M) prepared (generatorData j) bits
      iEq aEq nEq rEq (cap p n) setupBound
    rw [clock]
    simp only [generatorData, List.length_nil]
    simp only [cap, target] at *
    omega
  · have callCost := Source.call_cost (Output := Bool) M sourceSlots Symbol.source (sourceDecode M)
      (fun _ => .source .unit) (fun _ => .source .unit) (sourceBit M) prepared (cap p n) setupBound
    change (trialSetup M p).cost s + 1 + (sourceCall M).cost prepared ≤ _
    change (Source.call M sourceSlots Symbol.source (sourceDecode M) (fun _ => .source .unit)
      (fun _ => .source .unit) (sourceBit M)).cost prepared ≤ _ at callCost
    dsimp only [sourceCall]
    nlinarith

theorem takeOutput_bound (s : Store M) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((takeOutput M).eval s) budget ∧ (takeOutput M).cost s ≤ 9 * budget + 1 := by
  constructor
  · rw [takeOutput_eval]
    exact (sizes.clear 10).update 19 _ (by simpa using sizes 10)
  · have source := sizes 10
    have destination := sizes 19
    simp only [takeOutput, WordStack.Routine.seq, WordStack.Routine.clear,
      WordStack.Routine.transfer, Function.update_of_ne (by decide : (10 : Fin 35) ≠ 19)]
    omega

theorem offer_bound (s : Store M) (budget : ℕ) (sizes : StoreBound s budget) (positive : 1 ≤ budget) :
    StoreBound ((offer M).eval s) budget ∧ (offer M).cost s ≤ 120 * (budget + 1) := by
  unfold offer
  simp only [WordStack.Routine.branch]
  split
  · let a := (takeOutput M).eval s
    let b := (LengthTest.routine (O := Bool) lengthSlots (Symbol.unit : Cell M)).eval a
    obtain ⟨aBound, aCost⟩ := takeOutput_bound M s budget sizes
    have bBound := aBound.lengthTest (O := Bool) lengthSlots (Symbol.unit : Cell M) positive
    have bCost := LengthTest.routine_cost (O := Bool) lengthSlots (Symbol.unit : Cell M) a budget aBound
    have lastBound : StoreBound
        ((if (b 28).head?.isSome then
          WordStack.Routine.assign (O := Bool) 19 34 18 (by decide) (by decide) (by decide) id
        else WordStack.Routine.skip).eval b) budget := by
      split
      · exact bBound.assign (O := Bool) 19 34 18 (by decide) (by decide) (by decide) id
      · exact bBound
    have lastCost : (if (b 28).head?.isSome then
          WordStack.Routine.assign (O := Bool) 19 34 18 (by decide) (by decide) (by decide) id
        else WordStack.Routine.skip).cost b ≤ 20 * budget + 3 := by
      split
      · rw [WordStack.Routine.assign_cost]
        have h19 : (b 19).length ≤ budget := bBound 19
        have h34 : (b 34).length ≤ budget := bBound 34
        have h18 : (b 18).length ≤ budget := bBound 18
        omega
      · simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]
    refine ⟨lastBound, ?_⟩
    change 1 + ((takeOutput M).cost s + 1 +
      ((LengthTest.routine lengthSlots Symbol.unit).cost a + 1 +
        (1 + (if (b 28).head?.isSome then
          WordStack.Routine.assign (O := Bool) 19 34 18 (by decide) (by decide) (by decide) id
        else WordStack.Routine.skip).cost b))) ≤ _
    omega
  · exact ⟨sizes, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]; omega⟩

theorem trial_bound (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) (s : Store M)
    (h : Stored M n j bits answer s) (sizes : StoreBound s (cap p n))
    (index : j ≤ 2 * target n) (seed : bits.length ≤ p n + 1) :
    StoreBound ((trial M p).eval s) (cap p n) ∧ (trial M p).cost s ≤ trialBudget M p n := by
  let a := (sourceTrial M p).eval s
  let b := (offer M).eval a
  obtain ⟨aBound, aCost⟩ := sourceTrial_bound M p n j bits answer s h sizes index seed
  obtain ⟨bBound, bCost⟩ := offer_bound M a (cap p n) aBound (by simp [cap]; omega)
  have nextIndex : (b 13).length = j := by
    change ((offer M).eval ((sourceTrial M p).eval s) 13).length = j
    rw [offer_fixed M _ 13 (by tauto), sourceTrial_fixed M p s 13 (by tauto), h.index]
  constructor
  · change StoreBound (Function.update b 13 (.unit :: b 13)) _
    exact bBound.update 13 _ (by simp [nextIndex]; simp only [cap, target] at *; omega)
  · change (sourceTrial M p).cost s + 1 + ((offer M).cost a + 1 + 1) ≤ _
    dsimp only [trialBudget]
    nlinarith

def searchBudget (p : PolynomialBound) (n : ℕ) : ℕ :=
  trials n * (trialBudget M p n + 4)

theorem counted_bound (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) (s : Store M)
    (h : Stored M n j bits answer s) (sizes : StoreBound s (cap p n))
    (index : j ≤ 2 * target n) (seed : bits.length ≤ p n + 1) :
    StoreBound ((WordStack.Routine.counted 23 (trial M p)).eval s) (cap p n) ∧
      (WordStack.Routine.counted 23 (trial M p)).cost s ≤ trialBudget M p n + 2 := by
  let popped := Function.update s 23 (s 23).tail
  have stored : Stored M n j bits answer popped := by
    constructor <;> simp [popped, h.input, h.auxiliary, h.index, h.physical,
      h.random, h.targetLength, h.saved]
  have poppedBound : StoreBound popped (cap p n) :=
    sizes.update 23 _ (by simpa only [List.length_tail] using (Nat.sub_le (s 23).length 1).trans (sizes 23))
  obtain ⟨bound, cost⟩ := trial_bound M p n j bits answer popped stored poppedBound index seed
  refine ⟨bound, ?_⟩
  change 1 + 1 + (trial M p).cost popped ≤ _
  omega

theorem search_bound (p : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store M)
    (h : Stored M n 0 bits [] s) (sizes : StoreBound s (cap p n))
    (count : (s 23).length = trials n) (seed : bits.length ≤ p n + 1) :
    StoreBound ((search M p).eval s) (cap p n) ∧
      (search M p).cost s ≤ searchBudget M p n := by
  let f := (WordStack.Routine.counted 23 (trial M p)).eval
  have stored (k : ℕ) : Stored M n k bits (foldAnswer M p n bits 0 k []) (f^[k] s) := by
    simpa [f] using iterate_stored M p n 0 k bits [] s h
  have allBounds (k : ℕ) (hk : k ≤ trials n) : StoreBound (f^[k] s) (cap p n) := by
    induction k with
    | zero => exact sizes
    | succ k ih =>
      have previous := ih (by omega)
      have step := counted_bound M p n k bits (foldAnswer M p n bits 0 k []) (f^[k] s)
        (stored k) previous (by simp only [trials] at hk; omega) seed
      simpa only [Function.iterate_succ_apply'] using step.1
  constructor
  · change StoreBound (f^[(s 23).length] s) _
    rw [count]
    exact allBounds _ le_rfl
  · change WordStack.Routine.loopCost _ _ (s 23).length s ≤ _
    rw [count]
    apply (WordStack.Routine.loopCost_bound _ _ (trials n) (trialBudget M p n + 2) s ?_).trans
      (by simp [searchBudget])
    intro k hk
    exact (counted_bound M p n k bits (foldAnswer M p n bits 0 k []) (f^[k] s)
      (stored k) (allBounds k hk.le) (by simp only [trials] at hk; omega) seed).2

end
end ComplexityOfGenerators.Simulation.ExpectedCollisionSearch
