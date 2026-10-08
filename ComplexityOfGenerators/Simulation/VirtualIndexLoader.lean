import ComplexityOfGenerators.Simulation.VirtualIndexTime
import ComplexityOfGenerators.Simulation.BlockMarker
import ComplexityOfGenerators.Simulation.RoutineExecution
import ComplexityOfGenerators.Simulation.UnaryInput

/-! Initialisation of the virtual-index tracks for the collision reduction's
affine index. The complete finite transition table is a block loader followed
by the verified simulation routine, reading the physical unary index tape. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

def indexInitialCell : IndexCell M.symbols := ⟨none, true, true, true, true⟩

def indexLiveCell : IndexCell M.symbols := ⟨none, false, true, false, false⟩

def collisionIndexBlocks : InputBlocks Unit (IndexCell M.symbols) where
  leading := indexInitialCell M :: List.replicate 5 (indexLiveCell M)
  trailing := []
  block := fun _ => List.replicate 4 (indexLiveCell M)

omit [Fintype O] in
@[simp] theorem collisionIndexBlocks_word (n : ℕ) :
    (collisionIndexBlocks M).word (List.replicate n ()) =
      indexInitialCell M :: List.replicate (5 + 4 * n) (indexLiveCell M) := by
  simp only [InputBlocks.word, collisionIndexBlocks, List.flatMap_replicate,
    List.flatten_replicate_replicate, List.append_nil, List.cons_append, List.replicate_append_replicate]
  rw [Nat.mul_comm n 4]

def indexLoaderProgram : Turing.TM0.Machine (IndexCell M.symbols) Unit := fun _ _ => none

def indexLoader : Machine Unit Bool Unit :=
  blockMachine (indexLoaderProgram M) (Fintype.equivFin Unit) (indexAlphabet M) (collisionIndexBlocks M)

/-- The whole adapter, starting with a genuinely blank work tape. Its two phases
are the concrete loader and the concrete virtual-index routine. -/
def collisionIndexMachine : Machine Unit Bool O :=
  unarySwapMachine (sequenceMachine (indexLoader M) (virtualIndexRoutine M))

omit [Fintype O] in
theorem initial_index_memory (tailLength : ℕ) :
    VirtualIndexMemory M (tailLength + 1) (fun _ => none) (some 0) (some 0)
      (bootMemory (indexAlphabet M)
        (indexInitialCell M :: List.replicate tailLength (indexLiveCell M)) (tailLength + 1)) := by
  intro i
  by_cases marker : i = -1
  · subst i
    simp [bootMemory, indexRead, virtualIndexCell]
    rfl
  · by_cases origin : i = 0
    · subst i
      simp [bootMemory, indexRead, virtualIndexCell, indexInitialCell, bootDecode_encode]
    · by_cases inside : 0 ≤ i ∧ i < ((tailLength + 1 : ℕ) : ℤ)
      · have positive : 0 < i.toNat := by omega
        have bound : i.toNat - 1 < tailLength := by omega
        have lookup : (indexInitialCell M :: List.replicate tailLength (indexLiveCell M)).getD i.toNat default =
            indexLiveCell M := by
          conv_lhs => arg 2; rw [← Nat.sub_add_cancel positive]
          rw [List.getD_cons_succ]
          exact List.getD_replicate (indexLiveCell M) bound
        simp only [bootMemory, ite_eq_right marker, ite_eq_left inside]
        rw [indexRead, bootDecode_encode, lookup]
        simp only [virtualIndexCell, Option.some.injEq, origin, Ne.symm origin, inside, decide_false]
        rfl
      · simp only [bootMemory, ite_eq_right marker, ite_eq_right inside]
        simp only [virtualIndexCell, Option.some.injEq, origin, Ne.symm origin, inside, decide_false]
        rfl

end

end ComplexityOfGenerators.Simulation
