import ComplexityOfGenerators.Simulation.BlockBootstrap
import ComplexityOfGenerators.Simulation.FiniteSupport

/-! Acceptance equivalence for native machines that load a block encoding
from the original alphabet. Finite-support restriction and the library's TM1
compiler are reused with the new, fully operational bootstrap. -/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {I Γ Q : Type} [Fintype I] [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

omit [Fintype Γ] in
theorem blockMachine_accepts_iff (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString) :
    (blockMachine program control alphabet blocks).Accepts (decisionData input) bits ↔
      ∃ last : TM0.Cfg Γ Q, TM0.Reaches program (TM0.init (blocks.word input)) last ∧
        program last.q last.Tape.head = none := by
  let M := blockMachine program control alphabet blocks
  let sim := blockSimulator program control alphabet blocks
  let clock := 2 * (blocks.word input).length + 2 * input.length + 5
  obtain ⟨ready, related, bootstrap⟩ := block_bootstrap program control alphabet blocks input bits
  have prefixRun : M.runFrom (decisionData input) bits M.initialConfiguration clock =
      M.observe (decisionData input) bits ready := by
    rw [Machine.runFrom_initial]
    exact bootstrap
  have suffix (t : ℕ) : M.run (decisionData input) bits (clock + t) =
      M.runFrom (decisionData input) bits ready t := by
    rw [← Machine.runFrom_initial]
    exact M.runFrom_add (decisionData input) bits M.initialConfiguration ready _ prefixRun t
  constructor
  · rintro ⟨word, t, accepted⟩
    have later := M.run_halted_add (decisionData input) bits t (.accepted word) accepted clock
    rw [Nat.add_comm t, suffix] at later
    have empty := postSimulator_accepted_output sim (decisionData input) bits (TM0.init (blocks.word input))
      ready related t word later
    subst word
    exact (postSimulator_halting_iff sim (decisionData input) bits (TM0.init (blocks.word input)) ready related).mp
      ⟨t, later⟩
  · intro halted
    obtain ⟨t, accepted⟩ :=
      (postSimulator_halting_iff sim (decisionData input) bits (TM0.init (blocks.word input)) ready related).mpr halted
    exact ⟨[], clock + t, (suffix t).trans accepted⟩

omit [Fintype Γ] in
theorem blockMachine_accepts_iff_eval (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString) :
    (blockMachine program control alphabet blocks).Accepts (decisionData input) bits ↔
      (TM0.eval program (blocks.word input)).Dom := by
  rw [blockMachine_accepts_iff]
  change (∃ last : TM0.Cfg Γ Q, TM0.Reaches program (TM0.init (blocks.word input)) last ∧
    program last.q last.Tape.head = none) ↔
    (StateTransition.eval (TM0.step program) (TM0.init (blocks.word input))).Dom
  rw [Part.dom_iff_mem]
  apply exists_congr
  intro last
  rw [StateTransition.mem_eval]
  have stopped : TM0.step program last = none ↔ program last.q last.Tape.head = none := by
    simp [TM0.step]
  exact and_congr_right fun _ => stopped.symm

theorem native_recognizer_of_supported_post_blocks (program : TM0.Machine Γ Q)
    (support : Finset Q) (supported : TM0.Supports program (support : Set Q)) (blocks : InputBlocks I Γ) :
    ∃ native : Machine I Bool Unit, native.Deterministic ∧
      ∀ input bits, native.Accepts (decisionData input) bits ↔ (TM0.eval program (blocks.word input)).Dom := by
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
  let native := blockMachine restricted control alphabet blocks
  refine ⟨native, blockMachine_deterministic restricted control alphabet blocks, ?_⟩
  intro input bits
  rw [blockMachine_accepts_iff_eval]
  change (StateTransition.eval (TM0.step restricted) (TM0.init (blocks.word input))).Dom ↔
    (StateTransition.eval (TM0.step program) (TM0.init (blocks.word input))).Dom
  apply StateTransition.tr_eval_dom respects
  refine ⟨supported.1, ?_⟩
  have initial := TM0.map_init identity liftState (blocks.word input)
  simpa [identity] using initial

theorem native_recognizer_of_supported_tm1_blocks {σ : Type} [Fintype σ] [Inhabited σ]
    (program : Q → TM1.Stmt Γ Q σ) (support : Finset Q) (supported : TM1.Supports program support)
    (blocks : InputBlocks I Γ) :
    ∃ native : Machine I Bool Unit, native.Deterministic ∧
      ∀ input bits, native.Accepts (decisionData input) bits ↔ (TM1.eval program (blocks.word input)).Dom := by
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_supported_post_blocks
    (TM1to0.tr program) (TM1to0.trStmts program support) (TM1to0.tr_supports program supported) blocks
  refine ⟨native, deterministic, ?_⟩
  intro input bits
  rw [accepts input bits, TM1to0.tr_eval]

end ComplexityOfGenerators.Simulation
