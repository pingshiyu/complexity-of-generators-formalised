import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Output.Correctness
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.LoopBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.StateBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.HeaderBounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineResources

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Output

open Simulation.WordStack
open Routine

set_option backward.isDefEq.respectTransparency true

theorem headerPrefix_resources (budget : ℕ) :
    ResourceBound (headerPrefix (O := Symbol)) budget (budget+1) (30*(budget+2)) := by
  have copied := ResourceBound.assign (k := 64) (O := Symbol) 37 43 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) budget
  have result := copied.seq (ResourceBound.push (k := 64) (O := Symbol) 43 Symbol.separator budget)
  exact result.weaken le_rfl le_rfl (by omega)

theorem matrixSetup_resources (budget : ℕ) :
    ResourceBound (matrixSetup (O := Symbol)) budget budget (200*(budget+1)) := by
  have six := ResourceBound.assign (k := 64) (O := Symbol) 43 5 48 (by decide) (by decide) (by decide) (id : Symbol→Symbol) budget
  have five := (ResourceBound.assign (k := 64) (O := Symbol) 45 4 48 (by decide) (by decide) (by decide) (id : Symbol→Symbol) budget).seq six
  have four := (ResourceBound.assign (k := 64) (O := Symbol) 44 3 48 (by decide) (by decide) (by decide) (id : Symbol→Symbol) budget).seq five
  have three := (ResourceBound.assign (k := 64) (O := Symbol) 40 2 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) budget).seq four
  have two := (ResourceBound.assign (k := 64) (O := Symbol) 35 1 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) budget).seq three
  have one := (ResourceBound.assign (k := 64) (O := Symbol) 2 0 48 (by decide) (by decide) (by decide) (id : Symbol→Symbol) budget).seq two
  have result := (ResourceBound.clearMany (k := 64) (S := Symbol) (O := Symbol) [6,7,8,9,10,11,12,13,14] budget).seq one
  exact result.weaken le_rfl le_rfl (by simp only [List.length_cons,List.length_nil]; omega)

theorem matrixPrepare_resources (budget : ℕ) :
    ResourceBound (matrixPrepare (O := Symbol)) budget (budget+1) (300*(budget+2)) := by
  have headerBound : ResourceBound (header (O := Symbol)) budget (budget+1) (60*(budget+1)) := by
    intro s sizes
    exact ⟨header_bound s budget sizes,header_cost s budget sizes⟩
  have adapted := headerBound.rename low32 (by omega)
  have result := (ResourceBound.assign (k := 64) (O := Symbol) 32 2 48 (by decide) (by decide) (by decide) (id : Symbol→Symbol) budget).seq
    (adapted.seq (matrixSetup_resources (budget+1)))
  exact result.weaken le_rfl le_rfl (by omega)

theorem matrix_resources (budget : ℕ) :
    ResourceBound ((MatrixInsert.routine (O := Symbol)).rename low16) budget
      (10*(budget+2)^2) (100000*(budget+2)^4) := by
  have source : ResourceBound (MatrixInsert.routine (O := Symbol)) budget
      (10*(budget+2)^2) (100000*(budget+2)^4) := by
    intro s sizes
    exact MatrixInsert.routine_bound s budget (sizes.mono (by omega)) (sizes 1) (sizes 2)
  exact source.rename low16 (by nlinarith)

theorem finish_resources (budget : ℕ) :
    ResourceBound (finish (O := Symbol)) budget (4*budget+6) (200*(budget+3)) := by
  have transferred := ResourceBound.transfer (k := 64) (O := Symbol) 43 31 (by decide) (id : Symbol→Symbol) (2*budget+3)
  have cleared := (ResourceBound.clear (k := 64) (S := Symbol) (O := Symbol) 31 (2*budget+3)).seq transferred
  have marked := (ResourceBound.oneHot (O := Symbol) markSlots Symbol.bit (budget+1)).seq cleared
  have second := (ResourceBound.assign (k := 64) (O := Symbol) 40 47 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) (budget+1)).seq marked
  have first := (ResourceBound.assign (k := 64) (O := Symbol) 37 46 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) (budget+1)).seq second
  have pushed := (ResourceBound.push (k := 64) (O := Symbol) 43 Symbol.separator budget).seq first
  have result := (ResourceBound.assign (k := 64) (O := Symbol) 5 43 48 (by decide) (by decide) (by decide) (id : Symbol→Symbol) budget).seq pushed
  exact result.weaken le_rfl (by omega) (by omega)

def storeBudget (budget : ℕ) : ℕ := 40*(budget+5)^2+6
def stackBudget (budget : ℕ) : ℕ := 100000*(budget+5)^4+10000*(budget+5)^2+10000*(budget+5)

theorem routine_resources (budget : ℕ) :
    ResourceBound (routine (O := Symbol)) budget (storeBudget budget) (stackBudget budget) := by
  have tail := (matrix_resources (budget+3)).seq (finish_resources (10*(budget+5)^2))
  have prepared := (matrixPrepare_resources (budget+2)).seq tail
  have inserted := (ResourceBound.insertAt (O := Symbol) newRowSlots (Symbol.bit true) (Symbol.bit false) (budget+1)).seq prepared
  have result := (headerPrefix_resources budget).seq inserted
  simp only [Nat.add_assoc] at result
  exact result.weaken le_rfl (by unfold storeBudget; omega) (by
    unfold stackBudget
    simp only [show budget+(3+2)=budget+5 by omega]
    omega)

theorem routine_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := Symbol)).eval s) (storeBudget budget) ∧
      (routine (O := Symbol)).cost s≤stackBudget budget := routine_resources budget s sizes

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Output
