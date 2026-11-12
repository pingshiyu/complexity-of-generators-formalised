import ComplexityOfGenerators.Simulation.StarGenerator.SourceBounds
import ComplexityOfGenerators.Simulation.StarGenerator.Loops

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem innerLoop_bound (seed time : PolynomialBound) (table : Table α) (m steps j n cap : ℕ)
    (p : Option (List α) × BitString) (s : Store G) (stored : InnerStored G table m j p s)
    (tableBound : BoundedAt n (time n) table) (sizes : StoreBound s cap)
    (positive : 1 ≤ j) (remaining : j + steps ≤ m + 1) (mBound : m ≤ n)
    (indexBudget : n + 1 ≤ cap) (seedBudget : seed n ≤ cap) (timeBudget : time n + 1 ≤ cap)
    (sourceSpace : 1 + n + seed n + 3 * (time n + 1) ≤ cap) (wordBudget : n * time n ≤ cap) :
    let code := WordStack.Routine.counted 30 (innerStep G seed time)
    StoreBound (code.eval^[steps] s) cap ∧ WordStack.Routine.loopCost code.cost code.eval steps s ≤
      steps * (stepBudget G seed time n cap + 4) := by
  induction steps generalizing j p s with
  | zero => exact ⟨sizes, by simp [WordStack.Routine.loopCost]⟩
  | succ steps ih =>
    let popped := (Local.pop (30 : Fin 35)).eval s
    have popSize : StoreBound popped cap := sizes.update 30 _ (by
      change (s 30).tail.length ≤ cap
      simpa only [List.length_tail] using (Nat.sub_le (s 30).length 1).trans (sizes 30))
    have nextView := innerStep_correct G seed time table m j p popped stored.pop_clock positive (by omega)
    obtain ⟨nextSize, nextCost⟩ := innerStep_bound G seed time table m j n cap p popped stored.pop_clock
      tableBound popSize positive (by omega) mBound indexBudget seedBudget timeBudget sourceSpace wordBudget
    obtain ⟨lastSize, lastCost⟩ := ih (j + 1) (next G seed time table m j p) _ nextView nextSize (by omega) (by omega)
    refine ⟨lastSize, ?_⟩
    change (WordStack.Routine.counted 30 (innerStep G seed time)).cost s + 2 +
      WordStack.Routine.loopCost _ _ steps ((innerStep G seed time).eval popped) ≤ _
    have countCost : (WordStack.Routine.counted 30 (innerStep G seed time)).cost s =
        2 + (innerStep G seed time).cost popped := rfl
    rw [countCost, Nat.succ_mul]
    omega

theorem stageSetup_bound (s : Store G) (cap : ℕ) (sizes : StoreBound s cap)
    (nextTarget : (s 23).length + 1 ≤ cap) (positive : 1 ≤ cap) :
    StoreBound ((stageSetup G).eval s) cap ∧ (stageSetup G).cost s ≤ 60 * (cap + 1) := by
  let a := (WordStack.Routine.ofLocal (O := α) (Local.push 23 (Symbol.unit : Cell G))).eval s
  let b := (WordStack.Routine.assign (O := α) 23 30 33 (by decide) (by decide) (by decide) id).eval a
  let c := (WordStack.Routine.clear (O := α) 24).eval b
  let d := (WordStack.Routine.ofLocal (O := α) (Local.push 24 (Symbol.unit : Cell G))).eval c
  let e := (WordStack.Routine.clear (O := α) 31).eval d
  let f := (UnionGenerator.flag G G 32 false).eval e
  have aSize : StoreBound a cap := sizes.update 23 _ (by simpa [Action.apply] using nextTarget)
  obtain ⟨bSize, bCost⟩ := ConcatenationGenerator.assign_bound G G 23 30 33 (by decide) (by decide) (by decide) a cap aSize
  have cSize : StoreBound c cap := bSize.clear 24
  have dSize : StoreBound d cap := by
    apply cSize.update 24 _
    simpa [c, WordStack.Routine.clear, Action.apply] using positive
  have eSize : StoreBound e cap := dSize.clear 31
  obtain ⟨fSize, fCost⟩ := UnionGenerator.flag_bound G G 32 false e cap eSize positive
  obtain ⟨result, resultCost⟩ := ConcatenationGenerator.assign_bound G G 29 34 33
    (by decide) (by decide) (by decide) f cap fSize
  refine ⟨result, ?_⟩
  have cCost : (WordStack.Routine.clear (O := α) 24).cost b ≤ 3 * cap := by exact Nat.mul_le_mul_left 3 (bSize 24)
  have eCost : (WordStack.Routine.clear (O := α) 31).cost d ≤ 3 * cap := by exact Nat.mul_le_mul_left 3 (dSize 31)
  change 1 + 1 + ((WordStack.Routine.assign (O := α) 23 30 33 (by decide) (by decide) (by decide) id).cost a + 1 +
    ((WordStack.Routine.clear (O := α) 24).cost b + 1 + (1 + 1 +
    ((WordStack.Routine.clear (O := α) 31).cost d + 1 +
    ((UnionGenerator.flag G G 32 false).cost e + 1 +
    (WordStack.Routine.assign (O := α) 29 34 33 (by decide) (by decide) (by decide) id).cost f))))) ≤ _
  omega

noncomputable def stageBudget (seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  100 * (cap + 1) + n * (stepBudget G seed time n cap + 4)

theorem stageStep_bound (seed time : PolynomialBound) (m n cap : ℕ) (table : Table α) (bits : BitString)
    (s : Store G) (stored : OuterStored G m table bits s) (tableBound : BoundedAt n (time n) table)
    (sizes : StoreBound s cap) (targetBound : m + 1 ≤ n)
    (indexBudget : n + 1 ≤ cap) (seedBudget : seed n ≤ cap) (timeBudget : time n + 1 ≤ cap)
    (sourceSpace : 1 + n + seed n + 3 * (time n + 1) ≤ cap) (wordBudget : n * time n ≤ cap)
    (archiveBudget : (n + 1) * (n * time n + 1) ≤ cap) :
    StoreBound ((stageStep G seed time).eval s) cap ∧
      (stageStep G seed time).cost s ≤ stageBudget G seed time n cap := by
  let ready := (stageSetup G).eval s
  obtain ⟨readySize, readyCost⟩ := stageSetup_bound G s cap sizes (by rw [stored.target]; omega) (by omega)
  have initial := stageSetup_stored G m table bits s stored
  have clock := stageSetup_clock G m table bits s stored
  obtain ⟨loopSize, loopCost⟩ := innerLoop_bound G seed time table (m + 1) (m + 1) 1 n cap (none, bits)
    ready initial tableBound readySize (by omega) (by omega) targetBound indexBudget seedBudget timeBudget sourceSpace wordBudget
  have last := innerLoop_correct G seed time table (m + 1) (m + 1) 1 (none, bits) ready initial (by omega) (by omega)
  let code := WordStack.Routine.counted 30 (innerStep G seed time)
  let endStore := code.eval^[m + 1] ready
  let answer := stage G seed time table (m + 1) bits
  have result : InnerStored G table (m + 1) (m + 2) answer endStore := by
    simpa only [answer, endStore, code, stage, Nat.one_add, Nat.add_assoc] using last
  have newBound : BoundedAt n (time n) (table ++ [answer.1]) :=
    extend_bounded G seed time n (m + 1) (table, bits) tableBound stored.length
  have space : (entry G answer.1 ++ endStore 29).length ≤ cap := calc
    _ = (archive G (table ++ [answer.1])).length := by rw [result.archiveWord, archive_append]
    _ ≤ (n + 1) * (n * time n + 1) := archive_length_bounded G _ n (time n) newBound (by simp [stored.length]; omega)
    _ ≤ cap := archiveBudget
  obtain ⟨finalSize, finalCost⟩ := appendEntry_bound G endStore cap loopSize (by omega) answer.1 space result.word result.found
  constructor
  · change StoreBound ((appendEntry G).eval (code.eval^[(ready 30).length] ready)) cap
    rw [clock]
    exact finalSize
  · change (stageSetup G).cost s + 1 +
      (WordStack.Routine.loopCost code.cost code.eval (ready 30).length ready + 1 +
      (appendEntry G).cost (code.eval^[(ready 30).length] ready)) ≤ _
    rw [clock]
    change WordStack.Routine.loopCost code.cost code.eval (m + 1) ready ≤ _ at loopCost
    have allLoops : WordStack.Routine.loopCost code.cost code.eval (m + 1) ready ≤
        n * (stepBudget G seed time n cap + 4) :=
      loopCost.trans (Nat.mul_le_mul_right _ targetBound)
    change (stageSetup G).cost s + 1 +
      (WordStack.Routine.loopCost code.cost code.eval (m + 1) ready + 1 + (appendEntry G).cost endStore) ≤ _
    dsimp only [stageBudget]
    omega

theorem outerLoop_bound (seed time : PolynomialBound) (steps m n cap : ℕ)
    (p : Table α × BitString) (s : Store G) (stored : OuterStored G m p.1 p.2 s)
    (tableBound : BoundedAt n (time n) p.1) (sizes : StoreBound s cap) (remaining : m + steps ≤ n)
    (indexBudget : n + 1 ≤ cap) (seedBudget : seed n ≤ cap) (timeBudget : time n + 1 ≤ cap)
    (sourceSpace : 1 + n + seed n + 3 * (time n + 1) ≤ cap) (wordBudget : n * time n ≤ cap)
    (archiveBudget : (n + 1) * (n * time n + 1) ≤ cap) :
    let code := WordStack.Routine.counted 22 (stageStep G seed time)
    StoreBound (code.eval^[steps] s) cap ∧ WordStack.Routine.loopCost code.cost code.eval steps s ≤
      steps * (stageBudget G seed time n cap + 4) := by
  induction steps generalizing m p s with
  | zero => exact ⟨sizes, by simp [WordStack.Routine.loopCost]⟩
  | succ steps ih =>
    let popped := (Local.pop (22 : Fin 35)).eval s
    have popSize : StoreBound popped cap := sizes.update 22 _ (by
      change (s 22).tail.length ≤ cap
      simpa only [List.length_tail] using (Nat.sub_le (s 22).length 1).trans (sizes 22))
    have nextView := stageStep_correct G seed time m p.1 p.2 popped stored.pop_clock
    obtain ⟨nextSize, nextCost⟩ := stageStep_bound G seed time m n cap p.1 p.2 popped stored.pop_clock
      tableBound popSize (by omega) indexBudget seedBudget timeBudget sourceSpace wordBudget archiveBudget
    have nextBound := extend_bounded G seed time n (m + 1) p tableBound stored.length
    obtain ⟨lastSize, lastCost⟩ := ih (m + 1) (extend G seed time (m + 1) p) _ nextView nextBound nextSize (by omega)
    refine ⟨lastSize, ?_⟩
    change (WordStack.Routine.counted 22 (stageStep G seed time)).cost s + 2 +
      WordStack.Routine.loopCost _ _ steps ((stageStep G seed time).eval popped) ≤ _
    have countCost : (WordStack.Routine.counted 22 (stageStep G seed time)).cost s =
        2 + (stageStep G seed time).cost popped := rfl
    rw [countCost, Nat.succ_mul]
    omega

noncomputable def bodyBudget (seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  30 * (cap + 1) + n * (stageBudget G seed time n cap + 4)

theorem body_bound (sourceSeed sourceTime : PolynomialBound) (n read cap : ℕ) (bits : BitString)
    (sizes : StoreBound (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store cap)
    (indexBudget : n + 1 ≤ cap) (seedBudget : sourceSeed n ≤ cap) (timeBudget : sourceTime n + 1 ≤ cap)
    (sourceSpace : 1 + n + sourceSeed n + 3 * (sourceTime n + 1) ≤ cap) (wordBudget : n * sourceTime n ≤ cap)
    (archiveBudget : (n + 1) * (n * sourceTime n + 1) ≤ cap) :
    StoreBound ((body G sourceSeed sourceTime).eval
      (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store) cap ∧
    (body G sourceSeed sourceTime).cost
      (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store ≤
      bodyBudget G sourceSeed sourceTime n cap := by
  let start := (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store
  let a := (WordStack.Routine.assign (O := α) 13 22 33 (by decide) (by decide) (by decide) id).eval start
  let b := (WordStack.Routine.ofLocal (O := α) (Local.push 29 (someMarker G))).eval a
  let ready := (setup G).eval start
  obtain ⟨aSize, aCost⟩ := ConcatenationGenerator.assign_bound G G 13 22 33 (by decide) (by decide) (by decide) start cap sizes
  have bSize : StoreBound b cap := by
    apply aSize.update 29 _
    simp [a, start, WordStack.Routine.assign_eval, BoundedSource.preparedMemory, Action.apply]
    omega
  obtain ⟨readySize, flagCost⟩ := UnionGenerator.flag_bound G G 32 true b cap bSize (by omega)
  have initial : OuterStored G 0 [some []] bits ready := by
    constructor <;>
      simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval,
        BoundedSource.preparedMemory, archive, encoded, entry, UnionGenerator.held,
        UnionGenerator.letters, UnionGenerator.flagWord]
  have clock : (ready 22).length = n := by
    simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
      WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, BoundedSource.preparedMemory]
  have tableBound : BoundedAt n (sourceTime n) [some ([] : List α)] :=
    correct_initial (fun i (word : List α) => i ≤ n → word.length ≤ i * sourceTime n) (by simp)
  obtain ⟨resultSize, loopCost⟩ := outerLoop_bound G sourceSeed sourceTime n 0 n cap ([some []], bits) ready initial
    tableBound readySize (by omega) indexBudget seedBudget timeBudget sourceSpace wordBudget archiveBudget
  constructor
  · change StoreBound ((WordStack.Routine.counted 22 (stageStep G sourceSeed sourceTime)).eval^[(ready 22).length] ready) cap
    rw [clock]
    exact resultSize
  · change (setup G).cost start + 1 +
      WordStack.Routine.loopCost _ _ (ready 22).length ready ≤ _
    rw [clock]
    have setupCost : (setup G).cost start ≤ 23 * cap + 8 := by
      change (WordStack.Routine.assign (O := α) 13 22 33 (by decide) (by decide) (by decide) id).cost start + 1 +
        (1 + 1 + (UnionGenerator.flag G G 32 true).cost b) ≤ _
      omega
    dsimp only [bodyBudget]
    omega

end ComplexityOfGenerators.Simulation.StarGenerator
