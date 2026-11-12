import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Views
import ComplexityOfGenerators.Simulation.UnionGenerator.Bounds
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

theorem reset_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((reset G H).eval s) cap ∧ (reset G H).cost s ≤ 12 * cap + 7 := by
  have a := (sizes.clear 25).clear 26
  obtain ⟨b, bc⟩ := UnionGenerator.flag_bound G H 27 false _ cap a positive
  obtain ⟨c, cc⟩ := UnionGenerator.flag_bound G H 28 false _ cap b positive
  refine ⟨c, ?_⟩
  have h25 := sizes 25
  have h26 := sizes 26
  simp only [reset, WordStack.Routine.seq, WordStack.Routine.clear, Function.update_of_ne (by decide : (26 : Fin 35) ≠ 25)]
  omega

theorem assign_bound (src dst scratch : Fin 35) (sd : src ≠ dst) (st : src ≠ scratch)
    (dt : dst ≠ scratch) (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((WordStack.Routine.assign (O := α) src dst scratch sd st dt id).eval s) cap ∧
      (WordStack.Routine.assign (O := α) src dst scratch sd st dt id).cost s ≤ 20 * cap + 3 := by
  refine ⟨sizes.assign src dst scratch sd st dt id, ?_⟩
  have hs := sizes src
  have hd := sizes dst
  have ht := sizes scratch
  simp only [WordStack.Routine.assign_cost]
  omega

theorem save_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap)
    (words : (s 25).length + (s 26).length ≤ cap) :
    StoreBound ((save G H).eval s) cap ∧ (save G H).cost s ≤ 40 * cap + 10 := by
  constructor
  · rw [save_eval]
    exact ((sizes.clear 33).update 31 _ (by simpa using words)).update 32 _ (by simpa using positive)
  · have h25 := sizes 25
    have h26 := sizes 26
    have h31 := sizes 31
    have h32 := sizes 32
    have h33 := sizes 33
    simp [save, WordStack.Routine.seq, WordStack.Routine.assign_cost, WordStack.Routine.assign_eval,
      WordStack.Routine.copy, UnionGenerator.flag, WordStack.Routine.clear, WordStack.Routine.ofLocal,
      Local.push, Local.ticks]
    omega

theorem offerStored_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap)
    (words : (s 25).length + (s 26).length ≤ cap) :
    StoreBound ((offerStored G H).eval s) cap ∧ (offerStored G H).cost s ≤ 40 * cap + 14 := by
  have saved := save_bound G H s cap sizes positive words
  unfold offerStored
  simp only [WordStack.Routine.branch]
  split
  · exact ⟨sizes, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]⟩
  · simp only [WordStack.Routine.branch]
    split
    · exact ⟨sizes, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]⟩
    · simp only [WordStack.Routine.branch]
      split
      · exact ⟨saved.1, by omega⟩
      · simp only [WordStack.Routine.branch]
        split
        · exact ⟨saved.1, by omega⟩
        · exact ⟨sizes, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]⟩

theorem offerStored_fixes_index (s : Store G H) : (offerStored G H).eval s 23 = s 23 := by
  unfold offerStored
  simp only [WordStack.Routine.branch]
  split <;> try rfl
  simp only [WordStack.Routine.branch]
  split <;> try rfl
  simp only [WordStack.Routine.branch]
  split
  · simp [save_eval]
  · simp only [WordStack.Routine.branch]
    split <;> simp [save_eval, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]

theorem advance_bound (s : Store G H) (cap : ℕ) (sizes : StoreBound s cap)
    (nextIndex : (s 23).length + 1 ≤ cap) :
    StoreBound ((advance G H).eval s) cap ∧ (advance G H).cost s = 5 := by
  have a := sizes.update 17 (s 17).tail (by simpa only [List.length_tail] using (Nat.sub_le (s 17).length 1).trans (sizes 17))
  have b := a.update 23 (Symbol.unit :: s 23) (by simpa using nextIndex)
  have c := b.update 24 (s 24).tail (by simpa only [List.length_tail] using (Nat.sub_le (s 24).length 1).trans (sizes 24))
  exact ⟨by simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using c,
    rfl⟩

noncomputable def stepBudget (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n cap : ℕ) : ℕ :=
  ((Source.body G (Symbol.left : Source.Symbol G → Cell G H) (UnionGenerator.leftDecode G H)
      (Source.bank BoundedSource.sourceSlots)).bound +
    (Source.body H (Symbol.right : Source.Symbol H → Cell G H) (UnionGenerator.rightDecode G H)
      (Source.bank BoundedSource.sourceSlots)).bound + 600) * (cap + 1) +
    Command.counterBudget leftSeed n + Command.counterBudget leftTime n +
    Command.counterBudget rightSeed n + Command.counterBudget rightTime n


theorem splitStep_bound (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j cap : ℕ) (previous : Option (List α)) (bits : BitString) (s : Store G H)
    (stored : Stored G H n j previous bits s) (sizes : StoreBound s cap) (jBound : j ≤ n)
    (index : n + 1 ≤ cap)
    (leftSeedBound : leftSeed n ≤ cap) (leftTimeBound : leftTime n + 1 ≤ cap)
    (rightSeedBound : rightSeed n ≤ cap) (rightTimeBound : rightTime n + 1 ≤ cap)
    (leftSpace : 1 + n + leftSeed n + 3 * (leftTime n + 1) ≤ cap)
    (rightSpace : 1 + n + rightSeed n + 3 * (rightTime n + 1) ≤ cap)
    (wordSpace : leftTime n + rightTime n + 2 ≤ cap) :
    StoreBound ((splitStep G H leftSeed leftTime rightSeed rightTime).eval s) cap ∧
      (splitStep G H leftSeed leftTime rightSeed rightTime).cost s ≤
        stepBudget G H leftSeed leftTime rightSeed rightTime n cap := by
  let a := (WordStack.Routine.assign (O := α) 23 13 33 (by decide) (by decide) (by decide) id).eval
    ((reset G H).eval s)
  obtain ⟨resetSize, resetCost⟩ := reset_bound G H s cap sizes (by omega)
  obtain ⟨aSize, aCost⟩ := assign_bound G H 23 13 33 (by decide) (by decide) (by decide) _ cap resetSize
  have initial : UnionGenerator.Stored G H j bits none none a := by
    constructor <;> simp [a, WordStack.Routine.assign_eval, reset_eval, UnionGenerator.held,
      UnionGenerator.flagWord, stored.input, stored.auxiliary, stored.empty, stored.leftIndex, stored.random]
  have ls := leftSeed.monotone jBound
  have lt := leftTime.monotone jBound
  obtain ⟨lSize, lWord, lCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) (Symbol.unit : Cell G H) Symbol.bit G Symbol.left (UnionGenerator.leftDecode G H)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit G H) (fun _ => rfl)
      leftSeed leftTime a (generatorData j) bits
      (by simp [initial.input, generatorData]) (by simp [initial.auxiliary, generatorData])
      initial.index initial.random initial.empty cap aSize
      (by simpa [generatorData] using (by omega : j + 1 ≤ cap))
      (by simpa [generatorData] using (by omega : leftSeed j ≤ cap))
      (by simpa [generatorData] using (by omega : leftTime j + 1 ≤ cap))
      (by simpa [generatorData] using (by omega : 1 + j + leftSeed j + 3 * (leftTime j + 1) ≤ cap))
  let b := (UnionGenerator.leftFinish G H).eval ((UnionGenerator.leftTrial G H leftSeed leftTime).eval a)
  obtain ⟨bSize, bCost⟩ := UnionGenerator.leftFinish_bound G H _ cap lSize (by omega)
  have left := UnionGenerator.leftStep_stored G H leftSeed leftTime j bits none none a initial
  have bIndex24 : (b 24).length = n - j := by
    have first : b 24 = a 24 := leftStep_frame G H leftSeed leftTime a 24 (by decide) (by decide) (by decide)
    have eq : b 24 = s 24 := by rw [first]; simp [a, WordStack.Routine.assign_eval, reset_eval]
    exact (congrArg List.length eq).trans stored.rightIndex
  have bIndex23 : (b 23).length = j := by
    have first : b 23 = a 23 := leftStep_frame G H leftSeed leftTime a 23 (by decide) (by decide) (by decide)
    have eq : b 23 = s 23 := by rw [first]; simp [a, WordStack.Routine.assign_eval, reset_eval]
    exact (congrArg List.length eq).trans stored.leftIndex
  let c := (WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).eval b
  obtain ⟨cSize, cCost⟩ := assign_bound G H 24 13 33 (by decide) (by decide) (by decide) _ cap bSize
  have middle : UnionGenerator.Stored G H (n - j) (bits.drop (leftSeed j))
      (UnionGenerator.sourceValue G leftTime j (bits.take (leftSeed j))) none c := by
    constructor
    · simpa [c, WordStack.Routine.assign_eval] using left.input
    · simpa [c, WordStack.Routine.assign_eval] using left.auxiliary
    · simpa [c, WordStack.Routine.assign_eval] using bIndex24
    · simpa [c, WordStack.Routine.assign_eval] using left.random
    · simpa [c, WordStack.Routine.assign_eval] using left.empty
    · simpa [c, WordStack.Routine.assign_eval] using left.leftWord
    · simpa [c, WordStack.Routine.assign_eval] using left.leftFlag
    · simpa [c, WordStack.Routine.assign_eval] using left.rightWord
    · simpa [c, WordStack.Routine.assign_eval] using left.rightFlag
  have kBound : n - j ≤ n := Nat.sub_le n j
  have rs := rightSeed.monotone kBound
  have rt := rightTime.monotone kBound
  obtain ⟨rSize, rWord, rCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) (Symbol.unit : Cell G H) Symbol.bit H Symbol.right (UnionGenerator.rightDecode G H)
      (fun _ => rfl) (fun _ => .right .unit) (fun _ => .right .unit) (UnionGenerator.rightBit G H) (fun _ => rfl)
      rightSeed rightTime c (generatorData (n - j)) (bits.drop (leftSeed j))
      (by simp [middle.input, generatorData]) (by simp [middle.auxiliary, generatorData])
      middle.index middle.random middle.empty cap cSize
      (by simpa [generatorData] using (by omega : (n - j) + 1 ≤ cap))
      (by simpa [generatorData] using (by omega : rightSeed (n - j) ≤ cap))
      (by simpa [generatorData] using (by omega : rightTime (n - j) + 1 ≤ cap))
      (by simpa [generatorData] using (by omega : 1 + (n - j) + rightSeed (n - j) + 3 * (rightTime (n - j) + 1) ≤ cap))
  let d := (UnionGenerator.rightFinish G H).eval ((UnionGenerator.rightTrial G H rightSeed rightTime).eval c)
  obtain ⟨dSize, dCost⟩ := UnionGenerator.rightFinish_bound G H _ cap rSize (by omega)
  have dLeft : (d 25).length ≤ leftTime j + 1 := by
    have first : d 25 = c 25 := rightStep_frame G H rightSeed rightTime c 25 (by decide) (by decide) (by decide)
    have eq : d 25 = b 25 := by rw [first]; simp [c, WordStack.Routine.assign_eval]
    rw [eq]
    exact (UnionGenerator.leftFinish_output_length G H _).trans lWord
  have dRight : (d 26).length ≤ rightTime (n - j) + 1 :=
    (UnionGenerator.rightFinish_output_length G H _).trans rWord
  have dIndex23 : (d 23).length = j := by
    have first : d 23 = c 23 := rightStep_frame G H rightSeed rightTime c 23 (by decide) (by decide) (by decide)
    have eq : d 23 = b 23 := by rw [first]; simp [c, WordStack.Routine.assign_eval]
    exact (congrArg List.length eq).trans bIndex23
  obtain ⟨offeredSize, offeredCost⟩ := offerStored_bound G H d cap dSize (by omega) (by omega)
  obtain ⟨finalSize, finalCost⟩ := advance_bound G H ((offerStored G H).eval d) cap offeredSize
    (by rw [offerStored_fixes_index, dIndex23]; omega)
  refine ⟨finalSize, ?_⟩
  have lsc := (Command.counterBudget leftSeed).monotone jBound
  have ltc := (Command.counterBudget leftTime).monotone jBound
  have rsc := (Command.counterBudget rightSeed).monotone kBound
  have rtc := (Command.counterBudget rightTime).monotone kBound
  simp only [generatorData] at lCost rCost
  dsimp only [stepBudget]
  change (reset G H).cost s + 1 +
    ((WordStack.Routine.assign (O := α) 23 13 33 (by decide) (by decide) (by decide) id).cost ((reset G H).eval s) + 1 +
    ((UnionGenerator.leftTrial G H leftSeed leftTime).cost a + 1 +
    ((UnionGenerator.leftFinish G H).cost ((UnionGenerator.leftTrial G H leftSeed leftTime).eval a) + 1 +
    ((WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).cost b + 1 +
    ((UnionGenerator.rightTrial G H rightSeed rightTime).cost c + 1 +
    ((UnionGenerator.rightFinish G H).cost ((UnionGenerator.rightTrial G H rightSeed rightTime).eval c) + 1 + ((offerStored G H).cost d + 1 + (advance G H).cost ((offerStored G H).eval d)))))))) ≤ _
  change (WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).cost b ≤ _ at cCost
  change (UnionGenerator.leftTrial G H leftSeed leftTime).cost a ≤ _ at lCost
  change (UnionGenerator.rightTrial G H rightSeed rightTime).cost c ≤ _ at rCost
  change (UnionGenerator.leftFinish G H).cost ((UnionGenerator.leftTrial G H leftSeed leftTime).eval a) ≤ _ at bCost
  change (UnionGenerator.rightFinish G H).cost ((UnionGenerator.rightTrial G H rightSeed rightTime).eval c) ≤ _ at dCost
  nlinarith only [resetCost, aCost, bCost, cCost, dCost, lCost, rCost, offeredCost, finalCost, lsc, ltc, rsc, rtc]


theorem loop_bound (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n steps j cap : ℕ) (p : Option (List α) × BitString) (s : Store G H)
    (stored : Stored G H n j p.1 p.2 s) (sizes : StoreBound s cap) (remaining : j + steps ≤ n + 1)
    (index : n + 1 ≤ cap)
    (leftSeedBound : leftSeed n ≤ cap) (leftTimeBound : leftTime n + 1 ≤ cap)
    (rightSeedBound : rightSeed n ≤ cap) (rightTimeBound : rightTime n + 1 ≤ cap)
    (leftSpace : 1 + n + leftSeed n + 3 * (leftTime n + 1) ≤ cap)
    (rightSpace : 1 + n + rightSeed n + 3 * (rightTime n + 1) ≤ cap)
    (wordSpace : leftTime n + rightTime n + 2 ≤ cap) :
    let code := WordStack.Routine.counted 30 (splitStep G H leftSeed leftTime rightSeed rightTime)
    StoreBound (code.eval^[steps] s) cap ∧
      WordStack.Routine.loopCost code.cost code.eval steps s ≤
        steps * (stepBudget G H leftSeed leftTime rightSeed rightTime n cap + 4) := by
  induction steps generalizing j p s with
  | zero => exact ⟨sizes, by simp [WordStack.Routine.loopCost]⟩
  | succ steps ih =>
    let popped := (Local.pop (30 : Fin 35)).eval s
    have popSize : StoreBound popped cap := sizes.update 30 _ (by
      change (s 30).tail.length ≤ cap
      have := sizes 30
      simp only [List.length_tail]
      omega)
    have nextView := splitStep_correct G H leftSeed leftTime rightSeed rightTime n j p.1 p.2 popped stored.pop_clock
    obtain ⟨nextSize, nextCost⟩ := splitStep_bound G H leftSeed leftTime rightSeed rightTime n j cap p.1 p.2 popped
      stored.pop_clock popSize (by omega) index leftSeedBound leftTimeBound rightSeedBound rightTimeBound
      leftSpace rightSpace wordSpace
    obtain ⟨lastSize, lastCost⟩ := ih (j + 1) (next G H leftSeed leftTime rightSeed rightTime n j p) _
      nextView nextSize (by omega)
    refine ⟨lastSize, ?_⟩
    change (WordStack.Routine.counted 30 (splitStep G H leftSeed leftTime rightSeed rightTime)).cost s + 2 +
      WordStack.Routine.loopCost _ _ steps ((splitStep G H leftSeed leftTime rightSeed rightTime).eval popped) ≤ _
    have countCost : (WordStack.Routine.counted 30 (splitStep G H leftSeed leftTime rightSeed rightTime)).cost s =
        2 + (splitStep G H leftSeed leftTime rightSeed rightTime).cost popped := rfl
    rw [countCost, Nat.succ_mul]
    omega

noncomputable def bodyBudget (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n cap : ℕ) : ℕ :=
  80 * cap + 40 + (n + 1) * (stepBudget G H leftSeed leftTime rightSeed rightTime n cap + 4)

theorem body_bound (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n read cap : ℕ) (bits : BitString)
    (sizes : StoreBound (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store cap)
    (index : n + 1 ≤ cap)
    (leftSeedBound : leftSeed n ≤ cap) (leftTimeBound : leftTime n + 1 ≤ cap)
    (rightSeedBound : rightSeed n ≤ cap) (rightTimeBound : rightTime n + 1 ≤ cap)
    (leftSpace : 1 + n + leftSeed n + 3 * (leftTime n + 1) ≤ cap)
    (rightSpace : 1 + n + rightSeed n + 3 * (rightTime n + 1) ≤ cap)
    (wordSpace : leftTime n + rightTime n + 2 ≤ cap) :
    StoreBound ((body G H leftSeed leftTime rightSeed rightTime).eval
      (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store) cap ∧
      (body G H leftSeed leftTime rightSeed rightTime).cost
      (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store ≤
        bodyBudget G H leftSeed leftTime rightSeed rightTime n cap := by
  let start := (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G H) Symbol.bit n read bits).store
  let a := (WordStack.Routine.assign (O := α) 13 22 33 (by decide) (by decide) (by decide) id).eval start
  let b := (WordStack.Routine.assign (O := α) 13 24 33 (by decide) (by decide) (by decide) id).eval a
  let c := (WordStack.Routine.assign (O := α) 13 30 33 (by decide) (by decide) (by decide) id).eval b
  let ready := (setup G H).eval start
  obtain ⟨aSize, aCost⟩ := assign_bound G H 13 22 33 (by decide) (by decide) (by decide) start cap sizes
  obtain ⟨bSize, bCost⟩ := assign_bound G H 13 24 33 (by decide) (by decide) (by decide) a cap aSize
  obtain ⟨cSize, cCost⟩ := assign_bound G H 13 30 33 (by decide) (by decide) (by decide) b cap bSize
  have clock : (ready 30).length = n + 1 := by
    simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
      WordStack.Routine.ofLocal, Local.eval_push, BoundedSource.preparedMemory]
  have readySize : StoreBound ready cap := by
    apply cSize.update 30 _
    simpa [c, b, a, start, WordStack.Routine.assign_eval, BoundedSource.preparedMemory, Action.apply] using index
  have initial : Stored G H n 0 none bits ready := by
    constructor <;>
      simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.ofLocal, Local.eval_push, BoundedSource.preparedMemory,
        UnionGenerator.held, UnionGenerator.flagWord]
  obtain ⟨loopSize, loopCost⟩ := loop_bound G H leftSeed leftTime rightSeed rightTime n (n + 1) 0 cap
    (none, bits) ready initial readySize (by omega) index leftSeedBound leftTimeBound rightSeedBound rightTimeBound
    leftSpace rightSpace wordSpace
  let code := WordStack.Routine.counted 30 (splitStep G H leftSeed leftTime rightSeed rightTime)
  let last := code.eval^[n + 1] ready
  obtain ⟨finalSize, finalCost⟩ := assign_bound G H 22 13 33 (by decide) (by decide) (by decide) last cap loopSize
  constructor
  · change StoreBound ((WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide) id).eval
      (code.eval^[(ready 30).length] ready)) cap
    rw [clock]
    exact finalSize
  · change (setup G H).cost start + 1 +
      (WordStack.Routine.loopCost code.cost code.eval (ready 30).length ready + 1 +
      (WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide) id).cost
        (code.eval^[(ready 30).length] ready)) ≤ _
    rw [clock]
    change _ ≤ bodyBudget G H leftSeed leftTime rightSeed rightTime n cap
    have setupCost : (setup G H).cost start ≤ 60 * cap + 13 := by
      change (WordStack.Routine.assign (O := α) 13 22 33 (by decide) (by decide) (by decide) id).cost start + 1 +
        ((WordStack.Routine.assign (O := α) 13 24 33 (by decide) (by decide) (by decide) id).cost a + 1 +
        ((WordStack.Routine.assign (O := α) 13 30 33 (by decide) (by decide) (by decide) id).cost b + 1 + 1)) ≤ _
      omega
    change WordStack.Routine.loopCost code.cost code.eval (n + 1) ready ≤ _ at loopCost
    change (setup G H).cost start + 1 +
      (WordStack.Routine.loopCost code.cost code.eval (n + 1) ready + 1 +
      (WordStack.Routine.assign (O := α) 22 13 33 (by decide) (by decide) (by decide) id).cost last) ≤ _
    dsimp only [bodyBudget]
    omega

end ComplexityOfGenerators.Simulation.ConcatenationGenerator
