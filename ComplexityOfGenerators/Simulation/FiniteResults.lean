import ComplexityOfGenerators.Simulation.FiniteSupport

/-! Restriction to reachable finite control preserves the final tape as well
as termination. This strengthens the domain-only recognizer interface for use
by generators, whose computed values must subsequently be printed. -/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

/-- A finite implementation of a Post program, preserving its result tape.
The implementation is constructed below from a proved finite support. -/
structure FinitePostImplementation (program : TM0.Machine Γ Q) where
  Control : Type
  finiteControl : Fintype Control
  initialControl : Inhabited Control
  machine : TM0.Machine Γ Control
  result_correct : letI := initialControl
    ∀ input last, last ∈ StateTransition.eval (TM0.step program) (TM0.init input) →
      ∃ final, final ∈ StateTransition.eval (TM0.step machine) (TM0.init input) ∧ final.Tape = last.Tape

/-- Mathlib's machine-map simulation restricts labels without changing any
symbol of the tape, including its final head position. -/
def finitePostImplementation (program : TM0.Machine Γ Q)
    (support : Finset Q) (supported : TM0.Supports program (support : Set Q)) :
    FinitePostImplementation program := by
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
  refine ⟨↥support, inferInstance, inferInstance, restricted, ?_⟩
  intro input last evaluated
  have initial : (TM0.init input : TM0.Cfg Γ Q).q ∈ (support : Set Q) ∧
      (TM0.init input).map identity liftState = TM0.init input := by
    refine ⟨supported.1, ?_⟩
    simpa [identity] using TM0.map_init identity liftState input
  obtain ⟨final, related, result⟩ := StateTransition.tr_eval respects initial evaluated
  refine ⟨final, result, ?_⟩
  rw [← related.2]
  change last.Tape.map identity = last.Tape
  obtain ⟨symbol, left, right⟩ := last.Tape
  refine left.induction_on fun l => right.induction_on fun r => ?_
  simp [Tape.map, ListBlank.map_mk, identity]

end

end ComplexityOfGenerators.Simulation
