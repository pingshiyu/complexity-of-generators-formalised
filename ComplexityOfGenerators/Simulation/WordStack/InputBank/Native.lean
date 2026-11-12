import ComplexityOfGenerators.Simulation.WordStack.InputBank.Handoff
import ComplexityOfGenerators.SelfReducibility

/-! Quantitative native compilation for finite stack controllers on two
ordinary word inputs. The loading prefix is part of the proved runtime. -/

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank

open TransducerBank

set_option backward.isDefEq.respectTransparency false

variable {I A Q S O : Type} {k : ℕ} (P : Program Q S O k)
    (inputStack auxiliaryStack : Fin k) (encodeInput : I → S) (encodeAuxiliary : A → S)

def NoRandom : Prop := ∀ state cell index,
  match P.transition state cell index with | .random _ _ => False | _ => True

theorem bank_deterministic (pure : NoRandom P) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Deterministic := by
  intro state input auxiliary index origin cell
  cases state with
  | input => cases input <;> trivial
  | inputWrite letter => trivial
  | auxiliary => cases auxiliary <;> trivial
  | auxiliaryWrite letter => trivial
  | body state =>
    cases state with
    | push next stack symbol => trivial
    | ready state =>
      have source := pure state cell index
      cases command : P.transition state cell index with
      | accept => simp [bank, Program.bankTransition, command, mapInstruction]
      | reject => simp [bank, Program.bankTransition, command, mapInstruction]
      | random no yes => simp [command] at source
      | step next operation move emit =>
        cases operation <;> simp [bank, Program.bankTransition, command, mapInstruction]

variable [Fintype I] [Fintype A] [Fintype Q] [Fintype S] [Fintype O]

noncomputable def machine : Machine I A O :=
  TransducerBank.bankMachine (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary)

theorem machine_deterministic (pure : NoRandom P) :
    (machine P inputStack auxiliaryStack encodeInput encodeAuxiliary).Deterministic :=
  TransducerBank.bankMachine_deterministic _
    (bank_deterministic P inputStack auxiliaryStack encodeInput encodeAuxiliary pure)

def compileBudget (arguments controllerTicks : ℕ) : ℕ :=
  let total := 2 * arguments + 2 + 2 * controllerTicks
  1 + (total + 1) * (2 * total + 4)

theorem run_compiled (different : inputStack ≠ auxiliaryStack) (data : InputData I A) (bits : BitString)
    (controllerTicks : ℕ) (result : Outcome O)
    (execution : P.Executes data.index bits
      ((loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary data).at P.initial) controllerTicks result) :
    ∃ ticks, ticks ≤ compileBudget (data.input.length + data.auxiliary.length) controllerTicks ∧
      (machine P inputStack auxiliaryStack encodeInput encodeAuxiliary).run data bits ticks = .halted result := by
  let B := bank P inputStack auxiliaryStack encodeInput encodeAuxiliary
  obtain ⟨sourceTicks, sourceCost, sourceRun⟩ := P.executes_compiled execution (Nat.zero_le _)
  have copied := load_prefix P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits different
  have bodyRun := external_executes P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits sourceRun
  have all := copied.executes B bodyRun
  obtain ⟨ticks, cost, native⟩ := TransducerBank.bank_run B data bits _ _ all
  refine ⟨ticks, ?_, native⟩
  apply cost.trans
  unfold compileBudget
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul <;> omega

noncomputable def compiledTime (time : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (1 + (2 * Polynomial.X + 2 + 2 * time.asPolynomial + 1) *
    (2 * (2 * Polynomial.X + 2 + 2 * time.asPolynomial) + 4))

theorem compiledTime_bound (time : PolynomialBound) (arguments controllerTicks : ℕ)
    (bound : controllerTicks ≤ time arguments) : compileBudget arguments controllerTicks ≤ compiledTime time arguments := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ arguments)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
    Polynomial.eval_X, PolynomialBound.asPolynomial_eval]
  unfold compileBudget
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul <;> omega

/-- A proved compiler criterion: its witness is an actual finite controller
and verified primitive executions from the concrete loaded input stacks. -/
noncomputable def polynomialWordFunction (different : inputStack ≠ auxiliaryStack)
    (function : List I → List A → List O) (time : PolynomialBound) (pure : NoRandom P)
    (runs : ∀ input auxiliary bits,
      ∃ ticks ≤ time (input.length + auxiliary.length),
        P.Executes 0 bits
          ((loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary
            ({ input := input, auxiliary := auxiliary } : InputData I A)).at P.initial)
          ticks (.accepted (function input auxiliary))) : PolynomialWordFunction function where
  machine := machine P inputStack auxiliaryStack encodeInput encodeAuxiliary
  deterministic := machine_deterministic P inputStack auxiliaryStack encodeInput encodeAuxiliary pure
  time := compiledTime time
  timeBound := by
    intro input auxiliary bits
    obtain ⟨ticks, bound, execution⟩ := runs input auxiliary bits
    obtain ⟨nativeTicks, nativeCost, native⟩ := run_compiled P inputStack auxiliaryStack encodeInput encodeAuxiliary
      different ({ input := input, auxiliary := auxiliary } : InputData I A) bits ticks _ execution
    have totalCost := nativeCost.trans (compiledTime_bound time _ ticks bound)
    have padded := (machine P inputStack auxiliaryStack encodeInput encodeAuxiliary).run_halted_add
      ({ input := input, auxiliary := auxiliary } : InputData I A) bits nativeTicks
      (.accepted (function input auxiliary)) native
      (compiledTime time (input.length + auxiliary.length) - nativeTicks)
    exact ⟨_, by simpa only [Nat.add_sub_of_le totalCost] using padded⟩
  computes := by
    intro input auxiliary
    obtain ⟨ticks, _, execution⟩ := runs input auxiliary []
    obtain ⟨nativeTicks, _, native⟩ := run_compiled P inputStack auxiliaryStack encodeInput encodeAuxiliary
      different ({ input := input, auxiliary := auxiliary } : InputData I A) [] ticks _ execution
    exact ⟨nativeTicks, native⟩

end ComplexityOfGenerators.Simulation.WordStack.InputBank
