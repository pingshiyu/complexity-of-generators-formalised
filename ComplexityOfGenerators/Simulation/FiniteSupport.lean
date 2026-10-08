import ComplexityOfGenerators.Simulation.PostMachine
import ComplexityOfGenerators.ComplexityClasses

/-!
# Finitely supported library programs in the native model

Mathlib's compiler-generated machines may have an infinite label type. A finite
support contains every reachable label. We restrict to that support, using
Mathlib's proved machine-map simulation, and then compile to an actual finite
native transition table. This restriction is proved, not assumed.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Inhabited Q]

/-- Every finitely supported Post program has a deterministic recognizer in
the paper's model, accepting exactly when the source partial evaluation halts. -/
theorem native_recognizer_of_supported_post (program : TM0.Machine Γ Q)
    (support : Finset Q) (supported : TM0.Supports program (support : Set Q)) :
    ∃ native : Machine Γ Bool Unit, native.Deterministic ∧
      ∀ input bits, native.Accepts (decisionData input) bits ↔ (TM0.eval program input).Dom := by
  classical
  let : Inhabited ↥support := ⟨⟨default, supported.1⟩⟩
  let liftState : PointedMap Q ↥support :=
    ⟨fun q => if member : q ∈ support then ⟨q, member⟩ else default, by
      rw [dite_eq_left (show default ∈ support from supported.1)]
      rfl⟩
  let forgetState : ↥support → Q := Subtype.val
  let identity : PointedMap Γ Γ := ⟨id, rfl⟩
  let restricted := program.map identity identity liftState forgetState
  have alphabet_inverse : Function.RightInverse identity identity := by intro symbol; rfl
  have control_inverse : ∀ q ∈ (support : Set Q), forgetState (liftState q) = q := by
    intro q member
    change (if member : q ∈ support then (⟨q, member⟩ : ↥support) else default).val = q
    rw [dite_eq_left (show q ∈ support from member)]
  have respects := program.map_respects identity identity liftState forgetState
    supported alphabet_inverse control_inverse
  let control := Fintype.equivFin ↥support
  let alphabet := Fintype.equivFin Γ
  let native := postMachine restricted control alphabet
  refine ⟨native, postMachine_deterministic restricted control alphabet, ?_⟩
  intro input bits
  rw [postMachine_accepts_iff_eval]
  change (StateTransition.eval (TM0.step restricted) (TM0.init input)).Dom ↔
    (StateTransition.eval (TM0.step program) (TM0.init input)).Dom
  apply StateTransition.tr_eval_dom respects
  refine ⟨supported.1, ?_⟩
  have initial := TM0.map_init identity liftState input
  simpa [identity] using initial

/-- This membership statement uses the original `RE` definition, rather than
replacing it by Mathlib's halting semantics. -/
theorem supported_post_halting_language_in_re (program : TM0.Machine Γ Q)
    (support : Finset Q) (supported : TM0.Supports program (support : Set Q)) :
    {input | (TM0.eval program input).Dom} ∈ RE Γ := by
  obtain ⟨native, deterministic, accepts⟩ :=
    native_recognizer_of_supported_post program support supported
  exact ⟨native, deterministic, fun input => accepts input []⟩

/-- Mathlib's verified TM1-to-Post compiler supplies the finite support; the
native compiler then supplies the actual recognizer. No polynomial bound for
this composite compiler is asserted here. -/
theorem native_recognizer_of_supported_tm1 {σ : Type} [Fintype σ] [Inhabited σ]
    (program : Q → TM1.Stmt Γ Q σ) (support : Finset Q)
    (supported : TM1.Supports program support) :
    ∃ native : Machine Γ Bool Unit, native.Deterministic ∧
      ∀ input bits, native.Accepts (decisionData input) bits ↔ (TM1.eval program input).Dom := by
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_supported_post
    (TM1to0.tr program) (TM1to0.trStmts program support) (TM1to0.tr_supports program supported)
  refine ⟨native, deterministic, ?_⟩
  intro input bits
  rw [accepts input bits, TM1to0.tr_eval]

end ComplexityOfGenerators.Simulation
