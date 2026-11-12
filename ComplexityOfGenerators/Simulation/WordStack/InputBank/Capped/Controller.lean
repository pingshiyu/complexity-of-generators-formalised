import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped.Native

/-! Input-capped compilation for existing word-stack controllers. Bounds are
polynomials in the supplied unary index, including on oversized inputs. -/

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

open TransducerBank
set_option backward.isDefEq.respectTransparency false

variable {I A Q S O : Type} {k : ℕ}
variable [Fintype I] [Fintype A] [Fintype Q] [Fintype S] [Fintype O]
variable (P : Program Q S O k) (inputStack auxiliaryStack : Fin k)
    (encodeInput : I → S) (encodeAuxiliary : A → S)

noncomputable def controllerMachine : Machine I A O :=
  machine (InputBank.bank P inputStack auxiliaryStack encodeInput encodeAuxiliary) inputStack

def controllerBudget (index controllerTicks : ℕ) : ℕ :=
  compileBudget index (4 * index + 2 + 2 * controllerTicks)

theorem run_controller_compiled (different : inputStack ≠ auxiliaryStack)
    (data : InputData I A) (bits : BitString)
    (input : data.input.length ≤ data.index) (auxiliary : data.auxiliary.length ≤ data.index)
    (controllerTicks : ℕ) (result : Outcome O)
    (execution : P.Executes data.index bits
      ((loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary data).at P.initial) controllerTicks result) :
    ∃ ticks, ticks ≤ controllerBudget data.index controllerTicks ∧
      (controllerMachine P inputStack auxiliaryStack encodeInput encodeAuxiliary).run data bits ticks = .halted result := by
  let B := InputBank.bank P inputStack auxiliaryStack encodeInput encodeAuxiliary
  obtain ⟨sourceTicks, sourceCost, sourceRun⟩ := P.executes_compiled execution (Nat.zero_le _)
  have copied := load_prefix P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits different
  have bodyRun := external_executes P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits sourceRun
  have all := copied.executes B bodyRun
  obtain ⟨ticks, bound, run⟩ := run_compiled B inputStack data bits input auxiliary _ result all
  refine ⟨ticks, bound.trans ?_, run⟩
  apply compileBudget_mono
  omega

noncomputable def controllerTime (time : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (1 + (8 * Polynomial.X + 6 + 2 * time.asPolynomial + 1) *
      (2 * (8 * Polynomial.X + 6 + 2 * time.asPolynomial) + 4))

theorem controllerTime_bound (time : PolynomialBound) (index ticks : ℕ)
    (bound : ticks ≤ time index) : controllerBudget index ticks ≤ controllerTime time index := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ index)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_ofNat, Polynomial.eval_X, PolynomialBound.asPolynomial_eval]
  unfold controllerBudget compileBudget
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul <;> omega

theorem controller_oversized_run (data : InputData I A) (bits : BitString)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    ∃ ticks, ticks ≤ compileBudget data.index bits.length ∧
      (controllerMachine P inputStack auxiliaryStack encodeInput encodeAuxiliary).run data bits ticks = .halted .exhausted :=
  oversized_run _ _ data bits oversized

theorem controller_oversized_language (data : InputData I A)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    (controllerMachine P inputStack auxiliaryStack encodeInput encodeAuxiliary).generatedLanguage data = ∅ :=
  oversized_language _ _ data oversized

theorem controller_oversized_isGenerator (data : InputData I A)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    (controllerMachine P inputStack auxiliaryStack encodeInput encodeAuxiliary).IsGenerator data :=
  oversized_isGenerator _ _ data oversized

theorem controller_oversized_trial (data : InputData I A) (seed : ℕ)
    (oversized : data.index < data.input.length ∨ data.index < data.auxiliary.length) :
    (controllerMachine P inputStack auxiliaryStack encodeInput encodeAuxiliary).GeneratorTimeBound
      data seed (compileBudget data.index seed) :=
  oversized_trial _ _ data seed oversized

end ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped
