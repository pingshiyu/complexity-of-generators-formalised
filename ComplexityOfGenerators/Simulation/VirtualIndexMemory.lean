import ComplexityOfGenerators.Simulation.VirtualIndex

/-! Preservation of the five work-tape tracks while the concrete index routine
clears, moves, and reinstalls the two virtual head markers. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

variable {O : Type} (M : Machine Unit Bool O)
variable {length : ℕ} {work : ℤ → Option (Fin M.symbols)} {ih wh : Option ℤ}
variable {memory : ℤ → Option (Fin (Fintype.card (IndexCell M.symbols) + 1))}

theorem VirtualIndexMemory.clear_index (position : ℤ)
    (h : VirtualIndexMemory M length work (some position) wh memory) :
    VirtualIndexMemory M length work none wh
      (Function.update memory position (some (indexWrite M
        {indexRead M (memory position) with indexHead := false}))) := by
  unfold VirtualIndexMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp [indexRead_write, h, virtualIndexCell]
  · rw [Function.update_of_ne same, h]
    simp [virtualIndexCell, Ne.symm same]

theorem VirtualIndexMemory.place_index (position : ℤ)
    (h : VirtualIndexMemory M length work none wh memory) :
    VirtualIndexMemory M length work (some position) wh
      (Function.update memory position (some (indexWrite M
        {indexRead M (memory position) with indexHead := true}))) := by
  unfold VirtualIndexMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp [indexRead_write, h, virtualIndexCell]
  · rw [Function.update_of_ne same, h]
    simp [virtualIndexCell, Ne.symm same]

/-- A work step writes the source symbol and temporarily clears its head mark.
The unary-index contents and its independently positioned marker are preserved. -/
theorem VirtualIndexMemory.write_source (position : ℤ) (symbol : Option (Fin M.symbols))
    (h : VirtualIndexMemory M length work ih (some position) memory) :
    VirtualIndexMemory M length (Function.update work position symbol) ih none
      (Function.update memory position (some (indexWrite M
        {indexRead M (memory position) with source := symbol, workHead := false}))) := by
  unfold VirtualIndexMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp [indexRead_write, h, virtualIndexCell]
  · rw [Function.update_of_ne same, h]
    simp [virtualIndexCell, Function.update_of_ne same, Ne.symm same]

theorem VirtualIndexMemory.place_work (position : ℤ)
    (h : VirtualIndexMemory M length work ih none memory) :
    VirtualIndexMemory M length work ih (some position)
      (Function.update memory position (some (indexWrite M
        {indexRead M (memory position) with workHead := true}))) := by
  unfold VirtualIndexMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp [indexRead_write, h, virtualIndexCell]
  · rw [Function.update_of_ne same, h]
    simp [virtualIndexCell, Ne.symm same]

end

end ComplexityOfGenerators.Simulation
