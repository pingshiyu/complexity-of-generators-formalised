import ComplexityOfGenerators.Simulation.FixedBlockRetry.Value
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.BoundedSource
import ComplexityOfGenerators.Simulation.WordStack.RandomInput

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry

open WordStack

variable {S O : Type} [Fintype S] (unitSymbol : S) (bitSymbol : Bool → S)

def clearBlock : WordStack.Routine S O 35 :=
  (WordStack.Routine.clear 17).seq (WordStack.Routine.clear 34)

def collectCommand (width : PolynomialBound) : Command S O 35 :=
  (BoundedSource.counter unitSymbol bitSymbol 18 (by decide) width).command.seq
  ((clearBlock (S := S) (O := O)).command.seq
  ((Command.collect 18 34 bitSymbol).seq (Command.transfer 34 17 id)))

def collectedMemory (n count : ℕ) (block : BitString) (m : Memory S O 35) : Memory S O 35 :=
  {m with randomHead := m.randomHead + count, store :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update m.store 21 []) 19 (List.replicate (n + 1) unitSymbol)) 20 []) 18 [])
        17 (block.map bitSymbol)) 34 []}

noncomputable def collectBudget (width : PolynomialBound) (n cap : ℕ) : ℕ :=
  32 * cap + 12 * width n + Command.counterBudget width n + 20

/-- Collect one complete block from the current random head. A partial block
exhausts before the deterministic phase is entered. -/
theorem collect_runs_at_index (width : PolynomialBound) (n cap inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (head : m.indexHead ≤ inputIndex) (index : (m.store 13).length = n) (sizes : StoreBound m.store cap) :
    ∃ t ≤ collectBudget width n cap,
      (collectCommand (O := O) unitSymbol bitSymbol width).Runs inputIndex bits m t
        (if width n ≤ bits.length - m.randomHead then
          .done (collectedMemory unitSymbol bitSymbol n (width n)
            ((bits.drop m.randomHead).take (width n)) m) else .exhausted) := by
  let counted : Memory S O 35 := {m with store :=
    (BoundedSource.counter (O := O) unitSymbol bitSymbol 18 (by decide) width).eval m.store}
  let cleaned : Memory S O 35 := {counted with store := (clearBlock (S := S) (O := O)).eval counted.store}
  obtain ⟨counterTime, counterCost, counterRun⟩ :=
    (BoundedSource.counter (O := O) unitSymbol bitSymbol 18 (by decide) width).runs bits m head
  have counterBound := CounterRoutine.routine_cost (O := O) (BoundedSource.counterSlots 18 (by decide))
    width unitSymbol m.store cap sizes
  change (BoundedSource.counter (O := O) unitSymbol bitSymbol 18 (by decide) width).cost m.store ≤ _ at counterBound
  simp only [BoundedSource.counterSlots_apply, index] at counterBound
  obtain ⟨clearTime, clearCost, clearRun⟩ := (clearBlock (S := S) (O := O)).runs bits counted head
  have clearBound : (clearBlock (S := S) (O := O)).cost counted.store ≤ 6 * cap + 1 := by
    have s17 := sizes 17
    have s34 := sizes 34
    simp [clearBlock, WordStack.Routine.seq, WordStack.Routine.clear, counted,
      BoundedSource.counter, CounterRoutine.routine_eval]
    omega
  have count_eq : (cleaned.store 18).length = width n := by
    simp [cleaned, counted, clearBlock, WordStack.Routine.seq, WordStack.Routine.clear,
      BoundedSource.counter, CounterRoutine.routine_eval, index]
  have random_eq : cleaned.randomHead = m.randomHead := rfl
  have cleanedHead : cleaned.indexHead ≤ inputIndex := head
  have positive := width.positive n
  have clean34 : cleaned.store 34 = [] := by simp [cleaned, clearBlock, WordStack.Routine.seq, WordStack.Routine.clear]
  by_cases enough : width n ≤ bits.length - m.randomHead
  · have collectRun := Command.collect_full 18 34 (by decide) bitSymbol bits cleaned cleanedHead
      (by rw [count_eq, random_eq]; omega)
    let collected := Command.collected 18 34 bitSymbol bits cleaned (cleaned.store 18).length
    have transferRun := Command.transfer_runs 34 17 (by decide) (id : S → S) bits collected cleanedHead
    have wordLength : (collected.store 34).length = width n := by
      change ((((bits.drop cleaned.randomHead).take (cleaned.store 18).length).reverse.map bitSymbol) ++ cleaned.store 34).length = _
      rw [clean34]
      simp only [List.append_nil, List.length_map, List.length_reverse, List.length_take, List.length_drop,
        count_eq, random_eq, Nat.min_eq_left enough]
    have final : (collected.set 34 []).set 17 ((collected.store 34).reverse.map id ++ collected.store 17) =
        collectedMemory unitSymbol bitSymbol n (width n) ((bits.drop m.randomHead).take (width n)) m := by
      apply Configuration.ext <;> try rfl
      · simp [collected, Command.collected, random_eq, count_eq, collectedMemory]
      · funext j
        fin_cases j <;>
          simp [collected, Command.collected, cleaned, counted, clearBlock, WordStack.Routine.seq,
            WordStack.Routine.clear, BoundedSource.counter, CounterRoutine.routine_eval, Memory.set,
            random_eq, count_eq, index, collectedMemory, List.map_reverse]
    rw [final, wordLength] at transferRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ counterRun
      (Command.Runs.seq _ _ _ _ _ _ _ clearRun (Command.Runs.seq _ _ _ _ _ _ _ collectRun transferRun))
    refine ⟨counterTime + 1 + (clearTime + 1 + (6 * (cleaned.store 18).length + 1 + 6 * width n)), ?_, ?_⟩
    · change counterTime + 1 + (clearTime + 1 + (6 * (cleaned.store 18).length + 1 + 6 * width n)) ≤ _
      rw [count_eq]
      dsimp only [collectBudget]
      omega
    · simpa only [collectCommand, enough, ite_true] using run
  · obtain ⟨t, cost, collectRun⟩ := Command.collect_short 18 34 (by decide) bitSymbol bits cleaned cleanedHead
      (by simpa only [count_eq, random_eq] using (by omega : bits.length - m.randomHead < width n))
    have aborted := Command.Runs.seq_absent cleaned (Command.collect 18 34 bitSymbol)
      (Command.transfer 34 17 id) t collectRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ counterRun
      (Command.Runs.seq _ _ _ _ _ _ _ clearRun aborted)
    refine ⟨counterTime + 1 + (clearTime + 1 + t), ?_, ?_⟩
    · simp only [count_eq] at cost
      change counterTime + 1 + (clearTime + 1 + t) ≤ _
      dsimp only [collectBudget]
      omega
    · simpa only [collectCommand, enough, ite_false] using run

theorem collect_runs (width : PolynomialBound) (n cap : ℕ) (bits : BitString) (m : Memory S O 35)
    (head : m.indexHead ≤ n) (index : (m.store 13).length = n) (sizes : StoreBound m.store cap) :
    ∃ t ≤ collectBudget width n cap,
      (collectCommand (O := O) unitSymbol bitSymbol width).Runs n bits m t
        (if width n ≤ bits.length - m.randomHead then
          .done (collectedMemory unitSymbol bitSymbol n (width n)
            ((bits.drop m.randomHead).take (width n)) m) else .exhausted) :=
  collect_runs_at_index unitSymbol bitSymbol width n cap n bits m head index sizes

theorem collectedMemory_bound (n count : ℕ) (block : BitString) (m : Memory S O 35)
    (cap : ℕ) (sizes : StoreBound m.store cap) (index : n + 1 ≤ cap) (length : block.length ≤ cap) :
    StoreBound (collectedMemory unitSymbol bitSymbol n count block m).store cap :=
  (((((sizes.clear 21).update 19 _ (by simpa using index)).clear 20).clear 18).update
    17 _ (by simpa using length)).clear 34

end ComplexityOfGenerators.Simulation.FixedBlockRetry
