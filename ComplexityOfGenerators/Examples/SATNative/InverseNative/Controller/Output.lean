import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Prepare

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem emitSaved_runs {n : ℕ} (bits : BitString) (m : Memory) (index : m.indexHead ≤ n) :
    ∃ final, emitSaved.Runs n bits m (4*(m.store 34).length) (.done final) ∧
      final.output = m.output ++ m.store 34 := by
  refine ⟨Command.emitted 34 some m,Command.emitWord_runs (34 : Fin 35) some bits m index,?_⟩
  simp [Command.emitted]

theorem emitBuffer_runs {n : ℕ} (bits : BitString) (m : Memory) (index : m.indexHead ≤ n) :
    ∃ ticks ≤ 3*(m.store 28).length+10*(m.store 21).length+2, ∃ final,
      (NativeSubstitution.emitBuffer.rename slots).Runs n bits m ticks (.done final) ∧
        final.output = m.output ++ (m.store 21).reverse := by
  obtain ⟨ticks,cost,final,run,output⟩ := NativeSubstitution.emitBuffer_runs bits (m.project slots) index
  have copied := run.rename slots m
  have start : Memory.patch slots (m.project slots) m = m := Memory.patch_eq slots _ _ rfl
  rw [start] at copied
  refine ⟨ticks,cost,Memory.patch slots final m,copied,?_⟩
  change final.output = m.output ++ (m.store 21).reverse at output
  exact output

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
