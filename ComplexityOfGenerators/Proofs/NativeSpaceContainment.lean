import ComplexityOfGenerators.Foundations.SpaceConfigurations
import ComplexityOfGenerators.Foundations.ResourceBounds

/-!
# Elementary space containments for the retained machine model

These statements concern the native classes, independently of the imported
Complexitylib classes. In particular, the time-to-space step uses the native
accounting for a cell entered immediately before halting.
-/

namespace ComplexityOfGenerators

theorem p_subset_pspace {α : Type} [Fintype α] : P α ⊆ PSPACE α := by
  rintro L ⟨M, p, deterministic, time, language⟩
  let one : PolynomialBound := ⟨1, 0, by decide⟩
  refine ⟨M, p.add one, deterministic, fun w => ⟨p w.length, time w []⟩,
    ?_, language⟩
  intro w
  apply Machine.SpaceBound.mono M (Machine.TimeBound.spaceBound M (time w))
  simpa [one, PolynomialBound.eval] using p.add_le one w.length

theorem pspace_subset_re {α : Type} [Fintype α] : PSPACE α ⊆ RE α := by
  rintro L ⟨M, _, deterministic, _, _, language⟩
  exact ⟨M, deterministic, language⟩

end ComplexityOfGenerators
