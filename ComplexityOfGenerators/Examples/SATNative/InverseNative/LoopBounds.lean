import ComplexityOfGenerators.Examples.SATNative.InverseNative.StepBounds
import ComplexityOfGenerators.Simulation.WordStack.GrowingRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] inverseStep inverseRoutine

def parserInvariant (capacity active : ℕ) (s : Store) : Prop := ∃ state, Represents capacity active state s

private theorem parserInvariant_pop (capacity active : ℕ) (s : Store) (valid : parserInvariant capacity active s) :
    parserInvariant capacity active (Function.update s 16 (s 16).tail) := by
  obtain ⟨state, represented⟩ := valid
  exact ⟨state, NativeBody.popped_represents capacity active state s represented⟩

private theorem inverseStep_preserves {O : Type} (bit : Bool) (capacity active : ℕ) (s : Store)
    (valid : parserInvariant capacity active s) : parserInvariant capacity active ((inverseStep (O := O) bit).eval s) := by
  obtain ⟨state, represented⟩ := valid
  exact ⟨NativeBody.step capacity active state, inverseStep_represents bit capacity active state s represented⟩

private theorem inverseStep_grows {O : Type} (bit : Bool) (capacity active : ℕ) (more : active + 1 ≤ capacity)
    (s : Store) (budget : ℕ) (large : capacity + 1 ≤ budget) (valid : parserInvariant capacity active s)
    (sizes : StoreBound s budget) : StoreBound ((inverseStep (O := O) bit).eval s) (budget + (capacity + 1)) := by
  obtain ⟨state, represented⟩ := valid
  have bounded := inverseStep_bound (O := O) bit capacity active state s represented budget (by omega) sizes (by omega) more
  change StoreBound _ (budget + capacity + 1) at bounded
  simpa only [Nat.add_assoc] using bounded

private theorem inverseStep_cost_linear {O : Type} (bit : Bool) (capacity active : ℕ) (more : active + 1 ≤ capacity)
    (s : Store) (budget : ℕ) (large : capacity + 1 ≤ budget) (valid : parserInvariant capacity active s)
    (sizes : StoreBound s budget) : (inverseStep (O := O) bit).cost s ≤ (NativeBody.stepConstant + 300) * (budget + 1) := by
  obtain ⟨state, represented⟩ := valid
  exact inverseStep_cost bit capacity active state s represented budget (by omega) sizes (by omega) more

/-- The inverse reuses the generic proved resource calculus for a growing
finite routine; only the actual native step's bounds are instantiated here. -/
theorem inverseRoutine_growing_bound {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (large : capacity + 1 ≤ budget)
    (sizes : stackBound budget s) (more : active + 1 ≤ capacity) :
    stackBound (budget + (s 16).length * (capacity + 1)) ((inverseRoutine (O := O) bit).eval s) := by
  have result := Routine.iterate_growing_bound (16 : Fin 32) (inverseStep (O := O) bit)
    (parserInvariant capacity active) (capacity + 1) (capacity + 1)
    (parserInvariant_pop capacity active) (inverseStep_preserves bit capacity active)
    (inverseStep_grows bit capacity active more) (inverseStep_frame bit)
    s budget large ⟨state, represented⟩ sizes
  unfold inverseRoutine
  exact result.2

theorem inverseRoutine_cost_ceiling {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget ceiling : ℕ) (large : capacity + 1 ≤ budget)
    (sizes : stackBound budget s) (more : active + 1 ≤ capacity)
    (fits : budget + (s 16).length * (capacity + 1) ≤ ceiling) :
    (inverseRoutine (O := O) bit).cost s ≤ (s 16).length * ((NativeBody.stepConstant + 304) * (ceiling + 1)) := by
  have cost := Routine.iterate_growing_cost (16 : Fin 32) (inverseStep (O := O) bit)
    (parserInvariant capacity active) (capacity + 1) (capacity + 1) (NativeBody.stepConstant + 300)
    (parserInvariant_pop capacity active) (inverseStep_preserves bit capacity active)
    (inverseStep_grows bit capacity active more) (inverseStep_cost_linear bit capacity active more)
    (inverseStep_frame bit) s budget ceiling large ⟨state, represented⟩ sizes fits
  unfold inverseRoutine
  simpa [Nat.add_assoc, Nat.mul_assoc] using cost

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
