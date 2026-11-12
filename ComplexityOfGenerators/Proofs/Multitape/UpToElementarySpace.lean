import ComplexityOfGenerators.Proofs.Multitape.UpToElementary
import ComplexityOfGenerators.Simulation.TransducerBank.RegionDrain
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

/-- The empty boundary family drains on one stationary work cell. -/
theorem empty_mem_gspaceUpTo (space : ℕ → ℕ) (dominates : ∀ n, n ≤ space n) :
    (∅ : Language α) ∈ GSPACEUpTo α space := by
  let original := ComplexityOfGenerators.emptyUpToFamily α
  let family := ofNativeUpTo (∅ : Language α) original
  refine ⟨family, (fun _ => 1), ?_, ?_, ?_⟩
  · rw [show family.toUniformGenerators = ofNativeUniform original.toUniformGenerators from rfl,
      ofNativeUniform_language, nativeUpTo_language (∅ : Language α) original]
  · refine ⟨1, 1, by decide, ?_⟩
    intro n large
    simpa only [Nat.one_mul] using large.trans (dominates n)
  · intro n
    let M := Simulation.TransducerBank.Native.machine (ComplexityOfGenerators.emptyGenerator α)
    have radius : M.SpaceBound (generatorData n) 0 := by
      apply Simulation.TransducerBank.TapeBank.spaceBound_of_regionRuns M.program
      intro bits
      refine ⟨.exhausted, ?_⟩
      apply Simulation.TransducerBank.TapeBank.drain_inRegion M.program (generatorData n) bits M.program.initial
        (by intros; rfl) bits.length M.initialConfiguration rfl
        (by simp [MultitapeMachine.initialConfiguration, Simulation.TransducerBank.TapeBank.initialConfiguration])
        0 (M.program.initial_bounded _)
    have cells := M.cellSpaceBound_of_radius (generatorData n) 0 radius
    change M.CellSpaceBound (generatorData n) 1 at cells
    exact cells

end
end ComplexityOfGenerators.Multitape
