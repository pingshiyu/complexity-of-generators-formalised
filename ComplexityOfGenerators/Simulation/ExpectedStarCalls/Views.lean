import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Basic
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)
    (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

@[simp] theorem pathWord_cons (j : ℕ) (parts : List ℕ) :
    pathWord P encode (j::parts) = pathSymbol P encode .cut ::
      List.replicate j (pathSymbol P encode .unit) ++ pathWord P encode parts := by
  simp [pathWord, StarPaths.payload, List.map_append]

include retract in
theorem path_unit_block (j : ℕ) (parts : List ℕ) :
    ((List.replicate j (pathSymbol P encode .unit) ++ pathWord P encode parts).takeWhile (isUnit P decode) =
      List.replicate j (pathSymbol P encode .unit)) ∧
    ((List.replicate j (pathSymbol P encode .unit) ++ pathWord P encode parts).dropWhile (isUnit P decode) =
      pathWord P encode parts) := by
  have unit : isUnit P decode (pathSymbol P encode .unit) = true := by
    simp [isUnit, pathSymbol, retract .unit]
  induction j with
  | zero => cases parts <;> simp [pathWord, StarPaths.payload, List.takeWhile_cons, List.dropWhile_cons, isUnit, pathSymbol, retract .cut]
  | succ j ih => simp [List.replicate_succ, List.takeWhile_cons, List.dropWhile_cons, unit, ih.1, ih.2]

include retract in
theorem parseFactor_fields (s : Store (β := β) P) (j : ℕ) (parts : List ℕ)
    (path : s 31 = pathWord P encode (j::parts)) :
    (parseFactor P decode).eval s 31 = pathWord P encode parts ∧
      (parseFactor P decode).eval s 71 = List.replicate j (pathSymbol P encode .unit) := by
  have block := path_unit_block P encode decode retract j parts
  simp [parseFactor, Routine.seq, Routine.clear, Routine.ofLocal, Local.eval_pop,
    Routine.transferWhile, path, pathWord_cons, block.1, block.2]

theorem parseFactor_frame (s : Store (β := β) P) (k : Fin 80) (a : k ≠ 31) (b : k ≠ 71) :
    (parseFactor P decode).eval s k = s k := by
  simp [parseFactor, Routine.seq, Routine.clear, Routine.ofLocal, Local.eval_pop, Routine.transferWhile, a, b]

theorem not_inner (k : Fin 80) (high : 70 ≤ k.val) : k ∉ innerRegisters := by
  rintro member
  obtain ⟨i, _, equality⟩ := List.mem_map.mp member
  have same := congrArg (fun j : Fin 80 => j.val) equality
  change 35+i.val = k.val at same
  have := i.isLt
  omega

theorem setup_owned (s : Store (β := β) P) (i : Fin 35) :
    (setup P).eval s (innerSlots i) = (initialStore P (s 71).length i).map Sum.inr := by
  have first : innerSlots i ≠ (71 : Fin 80) := by
    intro same; have equality := congrArg (fun j : Fin 80 => j.val) same
    change 35+i.val = 71 at equality; have := i.isLt; omega
  have scratch : innerSlots i ≠ (73 : Fin 80) := by
    intro same; have equality := congrArg (fun j : Fin 80 => j.val) same
    change 35+i.val = 73 at equality; have := i.isLt; omega
  have included : innerSlots i ∈ innerRegisters := List.mem_map.mpr ⟨i, by simp, rfl⟩
  have readonly : (71 : Fin 80) ∉ innerRegisters := not_inner 71 (by decide)
  have thirteen : innerSlots i = innerSlots 13 ↔ i = 13 := innerSlots.injective.eq_iff
  have twentyTwo : innerSlots i = innerSlots 22 ↔ i = 22 := innerSlots.injective.eq_iff
  have never13 : (71 : Fin 80) ≠ innerSlots 13 := by decide
  have never22 : (71 : Fin 80) ≠ innerSlots 22 := by decide
  have scratch13 : innerSlots 13 ≠ (73 : Fin 80) := by decide
  have scratch22 : innerSlots 22 ≠ (73 : Fin 80) := by decide
  by_cases a : i = 13 <;> by_cases b : i = 22 <;>
    simp [setup, Routine.seq, Routine.assign_eval, Routine.clearMany_eval, initialStore, Function.update_apply, a, b,
    never13, never22, scratch13, scratch22,
    first, scratch, included, readonly, thirteen, twentyTwo, List.map_const']

theorem setup_frame (s : Store (β := β) P) (k : Fin 80) (outside : ∀ i, k ≠ innerSlots i)
    (scratch : k ≠ 73) : (setup P).eval s k = s k := by
  have nonmember : k ∉ innerRegisters := by
    rintro member
    obtain ⟨i, _, same⟩ := List.mem_map.mp member
    exact outside i same.symm
  simp [setup, Routine.seq, Routine.assign_eval, Routine.clearMany_eval, nonmember,
    outside 13, outside 22, scratch]

theorem initialStore_bound (j : ℕ) : StoreBound (initialStore P j) j := by
  intro i
  have scratch13 : innerSlots 13 ≠ (73 : Fin 80) := by decide
  have scratch22 : innerSlots 22 ≠ (73 : Fin 80) := by decide
  by_cases a : i = 13 <;> by_cases b : i = 22 <;> simp [initialStore, a, b]

theorem saveWord_fields (s : Store (β := β) P) :
    (saveWord P).eval s 70 = (s (innerSlots 31)).reverse ++ s 70 ∧
      (saveWord P).eval s 31 = s 31 := by
  simp [saveWord, Routine.transfer, innerSlots]

end ComplexityOfGenerators.Simulation.ExpectedStarCalls
