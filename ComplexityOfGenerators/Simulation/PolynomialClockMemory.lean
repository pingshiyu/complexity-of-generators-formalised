import ComplexityOfGenerators.Simulation.PolynomialClock

/-! Independent preservation of source symbols, digit markers, the origin,
and the source work-head marker during polynomial-clock operations. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

variable {I A O : Type} (M : Machine I A O) (p : PolynomialBound)
variable {length : ℕ} {work : ℤ → Option (Fin M.symbols)}
variable {digits : Fin p.degree → Option ℤ} {wh : Option ℤ}
variable {memory : ℤ → Option (Fin (Fintype.card (ClockCell M.symbols p.degree) + 1))}

theorem PolynomialClockMemory.clear_digit (digit : Fin p.degree) (position : ℤ)
    (atPosition : digits digit = some position)
    (h : PolynomialClockMemory M p length work digits wh memory) :
    PolynomialClockMemory M p length work (Function.update digits digit none) wh
      (Function.update memory position (some (clockWrite M p
        {clockRead M p (memory position) with
          digit := Function.update (clockRead M p (memory position)).digit digit false}))) := by
  unfold PolynomialClockMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp only [Function.update_self, clockRead_write, h, polynomialClockCell]
    congr 1
    funext j
    by_cases hj : j = digit <;> simp [hj]
  · rw [Function.update_of_ne same, h]
    simp only [polynomialClockCell]
    congr 1
    funext j
    by_cases hj : j = digit <;> simp [hj, atPosition, Ne.symm same]

theorem PolynomialClockMemory.place_digit (digit : Fin p.degree) (position : ℤ)
    (absent : digits digit = none)
    (h : PolynomialClockMemory M p length work digits wh memory) :
    PolynomialClockMemory M p length work (Function.update digits digit (some position)) wh
      (Function.update memory position (some (clockWrite M p
        {clockRead M p (memory position) with
          digit := Function.update (clockRead M p (memory position)).digit digit true}))) := by
  unfold PolynomialClockMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp only [Function.update_self, clockRead_write, h, polynomialClockCell]
    congr 1
    funext j
    by_cases hj : j = digit <;> simp [hj]
  · rw [Function.update_of_ne same, h]
    simp only [polynomialClockCell]
    congr 1
    funext j
    by_cases hj : j = digit <;> simp [hj, absent, Ne.symm same]

theorem PolynomialClockMemory.write_source (position : ℤ) (symbol : Option (Fin M.symbols))
    (h : PolynomialClockMemory M p length work digits (some position) memory) :
    PolynomialClockMemory M p length (Function.update work position symbol) digits none
      (Function.update memory position (some (clockWrite M p
        {clockRead M p (memory position) with source := symbol, workHead := false}))) := by
  unfold PolynomialClockMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp [clockRead_write, h, polynomialClockCell]
  · rw [Function.update_of_ne same, h]
    simp [polynomialClockCell, Function.update_of_ne same, Ne.symm same]

theorem PolynomialClockMemory.place_work (position : ℤ)
    (h : PolynomialClockMemory M p length work digits none memory) :
    PolynomialClockMemory M p length work digits (some position)
      (Function.update memory position (some (clockWrite M p
        {clockRead M p (memory position) with workHead := true}))) := by
  unfold PolynomialClockMemory at h ⊢
  intro i
  by_cases same : i = position
  · subst i
    simp [clockRead_write, h, polynomialClockCell]
  · rw [Function.update_of_ne same, h]
    simp [polynomialClockCell, Ne.symm same]

end

end ComplexityOfGenerators.Simulation
