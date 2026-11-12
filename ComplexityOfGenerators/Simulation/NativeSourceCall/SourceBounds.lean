import ComplexityOfGenerators.Simulation.NativeSourceCall.Ready

/-! Original native source paths have a connected visited interval of at most
elapsed-time plus one cells. Cleanup therefore has a linear first-moment cost. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
variable {O : Type} (M : Machine Unit Bool O)

theorem source_path_geometry (length : ℕ) (bits : BitString) (ticks : ℕ) (finish : Configuration M)
    (path : M.Steps (generatorData length) bits M.initialConfiguration ticks finish) : M.TapeGeometry finish := by
  induction path with
  | refl => exact M.initialConfiguration_geometry
  | @tail ticks current next path edge ih => exact M.next_geometry _ _ current next ih edge

theorem source_path_bound (length : ℕ) (bits : BitString) (ticks : ℕ) (finish : Configuration M)
    (path : M.Steps (generatorData length) bits M.initialConfiguration ticks finish) :
    M.ConfigurationBound (generatorData length) ticks finish := by
  induction path with
  | refl => exact M.initialConfiguration_bound _
  | @tail ticks current next path edge ih =>
      have bounded := M.next_executionBound (generatorData length) bits ticks current ih
      rw [edge] at bounded
      exact bounded

theorem source_path_visited (length : ℕ) (bits : BitString) (ticks : ℕ) (finish : Configuration M)
    (path : M.Steps (generatorData length) bits M.initialConfiguration ticks finish) : finish.visited.card≤ticks+1 :=
  (source_path_bound M length bits ticks finish path).visited

end ComplexityOfGenerators.Simulation.NativeSourceCall
