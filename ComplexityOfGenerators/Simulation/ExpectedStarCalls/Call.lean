import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Retry

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

structure CallPost (encode : StarPaths.Symbol → β) (before after : Memory (Cell (β := β) P) α 80)
    (j failures : ℕ) (parts : List ℕ) (word : List α) : Prop where
  origin : after.indexHead = before.indexHead
  random : after.randomHead = before.randomHead+(failures+1)*P.seed j
  output : after.output = []
  path : after.store 31 = pathWord P encode parts
  buffer : (after.store 70).filterMap (outputLetter P) = word.reverse ++ (before.store 70).filterMap (outputLetter P)
  buffer_length : (after.store 70).length ≤ (before.store 70).length+BoundedMachinePhase.cap P.seed P.clock j
  inner_sizes : ∀ i, (after.store (innerSlots i)).length ≤ BoundedMachinePhase.cap P.seed P.clock j
  factor : (after.store 71).length = j
  scratch : after.store 73 = []
  frame : ∀ k, (∀ i, k ≠ innerSlots i) → k ≠ 31 → k ≠ 70 → k ≠ 71 → k ≠ 73 → after.store k = before.store k

theorem setup_scratch (s : Store (β := β) P) : (setup P).eval s 73 = [] := by
  simp [setup, Routine.seq, Routine.assign_eval, Function.update_apply, innerSlots]

theorem outside_inner (k : Fin 80) (low : k.val < 35 ∨ 70 ≤ k.val) : ∀ i, k ≠ innerSlots i := by
  intro i same
  have equality := congrArg (fun j : Fin 80 => j.val) same
  change k.val = 35+i.val at equality
  have := i.isLt
  omega

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

include retract in
theorem call_runs_success (inputIndex j failures : ℕ) (parts : List ℕ) (word : List α) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode (j::parts)) (within : j ≤ inputIndex)
    (enough : m.randomHead+(failures+1)*P.seed j ≤ bits.length)
    (failed : ∀ k < failures, UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) = none)
    (success : UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+failures*P.seed j)).take (P.seed j)) = some word) :
    ∃ ticks ≤ (parseFactor P decode).cost m.store+1+
        ((setup P).cost ((parseFactor P decode).eval m.store)+1+
          ((failures+1)*callBudget P j+1+6*BoundedMachinePhase.cap P.seed P.clock j)),
      ∃ next, (call P decode).Runs inputIndex bits m ticks (.done next) ∧
        CallPost P encode m next j failures parts word := by
  let a : Memory (Cell (β := β) P) α 80 := {m with store := (parseFactor P decode).eval m.store}
  let b : Memory (Cell (β := β) P) α 80 := {a with store := (setup P).eval a.store}
  have parsed := parseFactor_fields P encode decode retract m.store j parts path
  change a.store 31 = pathWord P encode parts ∧ a.store 71 = List.replicate j (pathSymbol P encode .unit) at parsed
  have owned (i : Fin 35) : b.store (innerSlots i) = (initialStore P j i).map Sum.inr := by
    rw [show b.store (innerSlots i) = (setup P).eval a.store (innerSlots i) from rfl, setup_owned, parsed.2, List.length_replicate]
  obtain ⟨first, firstCost, firstRun⟩ := (parseFactor P decode).runs (n := inputIndex) bits m (by omega)
  obtain ⟨second, secondCost, secondRun⟩ := (setup P).runs (n := inputIndex) bits a (by change m.indexHead ≤ inputIndex; omega)
  obtain ⟨third, thirdCost, inner, thirdRun, innerState, innerOrigin, innerHead, payload⟩ :=
    retry_runs_success P inputIndex j failures word bits b origin empty owned within enough failed success
  let c : Memory (Cell (β := β) P) α 80 := Memory.patch innerSlots (inner.mapSymbols Sum.inr) b
  let next : Memory (Cell (β := β) P) α 80 := {c with store := (saveWord P).eval c.store}
  have cOrigin : c.indexHead = 0 := innerOrigin
  obtain ⟨last, lastCost, lastRun⟩ := (saveWord P).runs (n := inputIndex) bits c (by rw [cOrigin] <;> omega)
  have preparedFrame (k : Fin 80) (outside : ∀ i, k ≠ innerSlots i) (pathDiff : k ≠ 31)
      (factorDiff : k ≠ 71) (scratchDiff : k ≠ 73) : b.store k = m.store k := by
    change (setup P).eval a.store k = _
    rw [setup_frame P a.store k outside scratchDiff]
    exact parseFactor_frame P decode m.store k pathDiff factorDiff
  have cFrame (k : Fin 80) (outside : ∀ i, k ≠ innerSlots i) : c.store k = b.store k :=
    Memory.patchStore_outside innerSlots _ _ k outside
  have cBuffer : c.store 70 = m.store 70 := by
    rw [cFrame 70 (outside_inner 70 (Or.inr (by decide)))]
    exact preparedFrame 70 (outside_inner 70 (Or.inr (by decide))) (by decide) (by decide) (by decide)
  have sourcePayload : c.store (innerSlots 31) = (inner.store 31).map Sum.inr := by simp [c, Memory.patch, Memory.mapSymbols, Local.mapStore]
  have lastBound : last ≤ 6*BoundedMachinePhase.cap P.seed P.clock j := by
    change last ≤ (saveWord P).cost c.store at lastCost
    have size : (c.store (innerSlots 31)).length ≤ BoundedMachinePhase.cap P.seed P.clock j := by
      rw [sourcePayload, List.length_map]
      exact innerState.sizes 31
    exact lastCost.trans (Nat.mul_le_mul_left 6 size)
  change second ≤ (setup P).cost ((parseFactor P decode).eval m.store) at secondCost
  refine ⟨first+1+(second+1+(third+1+last)), by omega, next, ?_, ?_⟩
  · exact Command.Runs.seq _ _ _ _ _ _ _ firstRun
      (Command.Runs.seq _ _ _ _ _ _ _ secondRun (Command.Runs.seq _ _ _ _ _ _ _ thirdRun lastRun))
  · constructor
    · exact innerOrigin.trans origin.symm
    · exact innerHead
    · exact innerState.output
    · rw [show next.store 31 = c.store 31 from (saveWord_fields P c.store).2,
        cFrame 31 (outside_inner 31 (Or.inl (by decide)))]
      change (setup P).eval a.store 31 = _
      rw [setup_frame P a.store 31 (outside_inner 31 (Or.inl (by decide))) (by decide)]
      exact parsed.1
    · change ((saveWord P).eval c.store 70).filterMap (outputLetter P) = _
      rw [(saveWord_fields P c.store).1, sourcePayload, cBuffer]
      simp only [List.filterMap_append, List.filterMap_reverse, List.filterMap_map, outputLetter, Function.comp_def,
        Sum.elim_inr, payload]
    · change ((saveWord P).eval c.store 70).length ≤ _
      rw [(saveWord_fields P c.store).1, sourcePayload, cBuffer, List.length_append, List.length_reverse, List.length_map]
      have := innerState.sizes 31
      omega
    · intro i
      change ((saveWord P).eval c.store (innerSlots i)).length ≤ _
      have not70 : innerSlots i ≠ (70 : Fin 80) := by
        intro same; have equality := congrArg (fun k : Fin 80 => k.val) same
        change 35+i.val = 70 at equality; have := i.isLt; omega
      by_cases selected : i = 31
      · subst i
        simp [saveWord, Routine.transfer, not70]
      · have different : innerSlots i ≠ innerSlots 31 := fun equal => selected (innerSlots.injective equal)
        simp only [saveWord, Routine.transfer, Function.update_of_ne not70, Function.update_of_ne different]
        simpa [c, Memory.patch, Memory.mapSymbols, Local.mapStore] using innerState.sizes i
    · have saved : next.store 71 = c.store 71 := by simp [next, saveWord, Routine.transfer, innerSlots]
      rw [saved, cFrame 71 (outside_inner 71 (Or.inr (by decide)))]
      change ((setup P).eval a.store 71).length = _
      rw [setup_frame P a.store 71 (outside_inner 71 (Or.inr (by decide))) (by decide), parsed.2, List.length_replicate]
    · have saved : next.store 73 = c.store 73 := by simp [next, saveWord, Routine.transfer, innerSlots]
      rw [saved, cFrame 73 (outside_inner 73 (Or.inr (by decide)))]
      exact setup_scratch P a.store
    · intro k outside pathDiff outputDiff factorDiff scratchDiff
      have sourceDiff : k ≠ innerSlots 31 := outside 31
      change (saveWord P).eval c.store k = _
      simp only [saveWord, Routine.transfer, Function.update_of_ne outputDiff, Function.update_of_ne sourceDiff]
      rw [cFrame k outside]
      exact preparedFrame k outside pathDiff factorDiff scratchDiff

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
