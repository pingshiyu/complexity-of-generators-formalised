import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Call

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

theorem parseFactor_bound (decode : β → StarPaths.Symbol) (s : Store (β := β) P) (budget : ℕ)
    (sizes : StoreBound s budget) : StoreBound ((parseFactor P decode).eval s) budget := by
  let a := Function.update (Function.update s 71 []) 31 (s 31).tail
  have bounded : StoreBound a budget := (sizes.clear 71).update 31 (s 31).tail
    (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (sizes 31))
  have length : ((a 31).takeWhile (isUnit P decode)).length + ((a 31).dropWhile (isUnit P decode)).length = (a 31).length := by
    simpa only [List.length_append] using congrArg List.length (List.takeWhile_append_dropWhile :
      (a 31).takeWhile (isUnit P decode) ++ (a 31).dropWhile (isUnit P decode) = a 31)
  change StoreBound (Function.update (Function.update a 31 ((a 31).dropWhile (isUnit P decode))) 71
    (((a 31).takeWhile (isUnit P decode)).reverse.map id ++ a 71)) budget
  apply (bounded.update 31 _ (by have := bounded 31; omega)).update 71
  simp only [a, Function.update_of_ne (by decide : (71 : Fin 80) ≠ 31), Function.update_self,
    List.append_nil, List.length_map, List.length_reverse]
  have source := bounded 31
  change ((a 31).takeWhile (isUnit P decode)).length ≤ budget
  omega

theorem parseFactor_cost (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode) (s : Store (β := β) P) (budget j : ℕ) (parts : List ℕ)
    (sizes : StoreBound s budget) (path : s 31 = pathWord P encode (j::parts)) :
    (parseFactor P decode).cost s ≤ 10*(budget+1) := by
  have factor : j ≤ budget := by
    have bounded := sizes 31
    rw [path, pathWord_cons] at bounded
    simp only [List.length_cons, List.length_append, List.length_replicate] at bounded
    omega
  have block := (path_unit_block P encode decode retract j parts).1
  change 3*(s 71).length+1+(1+1+6*(((s 31).tail).takeWhile (isUnit P decode)).length) ≤ _
  rw [path, pathWord_cons]
  simp only [List.cons_append, List.tail_cons]
  rw [block, List.length_replicate]
  have := sizes 71
  omega

theorem setup_bound (s : Store (β := β) P) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((setup P).eval s) budget ∧ (setup P).cost s ≤ 200*(budget+1) := by
  let a := (Routine.clearMany (O := α) innerRegisters).eval s
  let b := (Routine.assign (O := α) 71 (innerSlots 13) 73 (by decide) (by decide) (by decide)
    (fun _ => Sum.inr (UnionGenerator.Symbol.unit : InnerCell P))).eval a
  have aBound : StoreBound a budget := sizes.clearMany _
  have bBound : StoreBound b budget := aBound.assign _ _ _ _ _ _ _
  have clearing := Routine.clearMany_cost (O := α) innerRegisters s budget (fun j _ => sizes j)
  have length : innerRegisters.length = 35 := by simp [innerRegisters]
  rw [length] at clearing
  refine ⟨bBound.assign 71 (innerSlots 22) 73 (by decide) (by decide) (by decide) _, ?_⟩
  have a1 := aBound (innerSlots 13); have a2 := aBound 73; have a3 := aBound 71
  have b1 := bBound (innerSlots 22); have b2 := bBound 73; have b3 := bBound 71
  change (Routine.clearMany (O := α) innerRegisters).cost s+1+
    ((Routine.assign (O := α) 71 (innerSlots 13) 73 (by decide) (by decide) (by decide)
      (fun _ => Sum.inr (UnionGenerator.Symbol.unit : InnerCell P))).cost a+1+
      (Routine.assign (O := α) 71 (innerSlots 22) 73 (by decide) (by decide) (by decide)
        (fun _ => Sum.inr (UnionGenerator.Symbol.unit : InnerCell P))).cost b) ≤ _
  simp only [Routine.assign_cost]
  omega

theorem CallPost.store_bound {encode : StarPaths.Symbol → β} {m next : Memory (Cell (β := β) P) α 80}
    {j failures : ℕ} {parts : List ℕ} {word : List α} (post : CallPost P encode m next j failures parts word)
    (budget : ℕ) (sizes : StoreBound m.store budget) (path : m.store 31 = pathWord P encode (j::parts)) :
    StoreBound next.store (budget+BoundedMachinePhase.cap P.seed P.clock j) := by
  have pathSize := sizes 31
  rw [path, pathWord_cons] at pathSize
  simp only [List.length_cons, List.length_append, List.length_replicate] at pathSize
  intro k
  by_cases owned : ∃ i, innerSlots i = k
  · obtain ⟨i, rfl⟩ := owned
    exact (post.inner_sizes i).trans (by omega)
  · have outside : ∀ i, k ≠ innerSlots i := by intro i same; exact owned ⟨i, same.symm⟩
    by_cases pathReg : k = 31
    · subst k; rw [post.path]; omega
    by_cases bufferReg : k = 70
    · subst k; exact post.buffer_length.trans (Nat.add_le_add_right (sizes 70) _)
    by_cases factorReg : k = 71
    · subst k; rw [post.factor]; omega
    by_cases scratchReg : k = 73
    · subst k; simp only [post.scratch, List.length_nil]; omega
    rw [post.frame k outside pathReg bufferReg factorReg scratchReg]
    exact (sizes k).trans (by omega)

theorem polynomial_mono (p : PolynomialBound) {a b : ℕ} (bound : a ≤ b) : p a ≤ p b := by
  change p.coefficient*(a+1)^p.degree ≤ p.coefficient*(b+1)^p.degree
  exact Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega) _)

theorem callBudget_mono {j n : ℕ} (bound : j ≤ n) : callBudget P j ≤ callBudget P n := by
  have width := polynomial_mono P.seed bound
  have cap := polynomial_mono (BoundedMachinePhase.cap P.seed P.clock) bound
  have time := polynomial_mono (BoundedMachinePhase.time P.machine P.seed P.clock) bound
  have counter := polynomial_mono (Command.counterBudget P.seed) bound
  unfold callBudget FixedBlockRetry.attemptBudget FixedBlockRetry.collectBudget
  omega

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

include retract in
theorem call_runs_success_bounded (inputIndex j failures budget : ℕ) (parts : List ℕ) (word : List α) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (sizes : StoreBound m.store budget) (path : m.store 31 = pathWord P encode (j::parts)) (within : j ≤ inputIndex)
    (enough : m.randomHead+(failures+1)*P.seed j ≤ bits.length)
    (failed : ∀ k < failures, UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) = none)
    (success : UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+failures*P.seed j)).take (P.seed j)) = some word) :
    ∃ ticks ≤ (failures+1)*callBudget P j+300*(budget+BoundedMachinePhase.cap P.seed P.clock j+1),
      ∃ next, (call P decode).Runs inputIndex bits m ticks (.done next) ∧
        CallPost P encode m next j failures parts word ∧
        StoreBound next.store (budget+BoundedMachinePhase.cap P.seed P.clock j) := by
  obtain ⟨ticks, clock, next, run, post⟩ := call_runs_success P encode decode retract inputIndex j failures parts word bits m
    origin empty path within enough failed success
  have first := parseFactor_cost P encode decode retract m.store budget j parts sizes path
  have source := parseFactor_bound P decode m.store budget sizes
  have second := (setup_bound P _ budget source).2
  exact ⟨ticks, by omega, next, run, post, CallPost.store_bound P post budget sizes path⟩

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
