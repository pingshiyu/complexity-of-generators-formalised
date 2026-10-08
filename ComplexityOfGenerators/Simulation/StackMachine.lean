import ComplexityOfGenerators.Simulation.FiniteSupport
import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Reusing Mathlib's stack-machine compiler

The source input is encoded with Mathlib's own `TM2to1.trInit`. The verified
library simulations are composed with our concrete native compiler. This gives
halting-language recognizers, with no unproved polynomial simulation claim.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {K Q σ : Type} {Δ : K → Type}
variable [Fintype K] [DecidableEq K] [∀ k, Fintype (Δ k)]
variable [Inhabited Q] [Fintype σ] [Inhabited σ]

theorem native_recognizer_of_supported_tm2 (program : Q → TM2.Stmt Δ Q σ)
    (support : Finset Q) (supported : TM2.Supports program support) :
    ∃ native : Machine (TM2to1.Γ' K Δ) Bool Unit, native.Deterministic ∧
      ∀ k input bits, native.Accepts (decisionData (TM2to1.trInit k input)) bits ↔
        (TM2.eval program k input).Dom := by
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_supported_tm1
    (TM2to1.tr program) (TM2to1.trSupp program support) (TM2to1.tr_supports program supported)
  refine ⟨native, deterministic, ?_⟩
  intro k input bits
  rw [accepts (TM2to1.trInit k input) bits, TM2to1.tr_eval_dom]

end ComplexityOfGenerators.Simulation
