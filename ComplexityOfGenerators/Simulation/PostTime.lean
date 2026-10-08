import ComplexityOfGenerators.Simulation.UnaryBlockLoader

/-!
# Quantitative transfer from Mathlib Post executions

The existing Post compiler executes each source move or write in one native
transition. Here that correspondence is proved with the explicit step count
from Mathlib's `StateTransition.EvalsToInTime`, including the input-loading cost.
This does not assert a polynomial bound for Mathlib's partial-recursive compiler:
a time certificate for the particular source Post program is required.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {Γ Q I : Type} [Inhabited Γ] [Inhabited Q]
variable {program : TM0.Machine Γ Q}

/-- Every finite source path preserves its exact primitive-transition count. -/
theorem postSimulator_reaches_in_steps (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source last : TM0.Cfg Γ Q)
    (target : Configuration sim.machine) (related : PostRelated sim source target)
    (t : ℕ)
    (path : (fun c : Option (TM0.Cfg Γ Q) => c.bind (TM0.step program))^[t] (some source) = some last) :
    ∃ nextTarget, PostRelated sim last nextTarget ∧
      sim.machine.runFrom data bits target t = sim.machine.observe data bits nextTarget := by
  induction t generalizing last with
  | zero =>
      have same : source = last := Option.some.inj path
      subst last
      exact ⟨target, related, rfl⟩
  | succ t ih =>
      rw [Function.iterate_succ_apply'] at path
      cases previous : (fun c : Option (TM0.Cfg Γ Q) => c.bind (TM0.step program))^[t]
          (some source) with
      | none => simp [previous] at path
      | some current =>
          have step : TM0.step program current = some last := by simpa [previous] using path
          obtain ⟨currentTarget, currentRelated, execution⟩ := ih current previous
          obtain ⟨live, nextTarget, next, nextRelated⟩ :=
            postSimulator_step sim data bits current last currentTarget currentRelated step
          exact ⟨nextTarget, nextRelated, by simp only [Machine.runFrom, execution, live, next]⟩

/-- A Mathlib time certificate gives a native execution with the same time
budget. Observing the final halting instruction costs no additional step. -/
theorem postSimulator_halts_in_time (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source last : TM0.Cfg Γ Q)
    (target : Configuration sim.machine) (related : PostRelated sim source target)
    (t : ℕ) (execution : StateTransition.EvalsToInTime (TM0.step program) source (some last) t)
    (halted : program last.q last.Tape.head = none) :
    sim.machine.runFrom data bits target t = .halted (.accepted []) := by
  obtain ⟨nextTarget, nextRelated, path⟩ := postSimulator_reaches_in_steps sim data bits
    source last target related execution.steps execution.evals_in_steps
  have observation := postSimulator_observe_halted sim data bits last nextTarget nextRelated halted
  have padding := sim.machine.runFrom_add data bits target nextTarget execution.steps path
    (t - execution.steps)
  rw [Nat.add_sub_of_le execution.steps_le_m] at padding
  exact padding.trans (sim.machine.runFrom_halted data bits nextTarget (.accepted []) observation _)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable [Fintype Γ] [Fintype I] {states symbols : ℕ}

omit [Fintype Γ] in
/-- End-to-end native execution, from a blank work tape, with the source time
certificate added to the exact cost of loading the input encoding. -/
theorem blockMachine_timeBound (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I)
    (last : TM0.Cfg Γ Q) (t : ℕ)
    (execution : StateTransition.EvalsToInTime (TM0.step program)
      (TM0.init (blocks.word input)) (some last) t)
    (halted : program last.q last.Tape.head = none) :
    (blockMachine program control alphabet blocks).TimeBound (decisionData input)
      (2 * (blocks.word input).length + 2 * input.length + 5 + t) := by
  intro bits
  obtain ⟨ready, related, loaded⟩ := block_bootstrap program control alphabet blocks input bits
  have simulated := postSimulator_halts_in_time (blockSimulator program control alphabet blocks)
    (decisionData input) bits _ last ready related t execution halted
  have joined := (blockMachine program control alphabet blocks).runFrom_add (decisionData input) bits
    (blockMachine program control alphabet blocks).initialConfiguration ready
    (2 * (blocks.word input).length + 2 * input.length + 5) (by simpa using loaded) t
  exact ⟨.accepted [], by simpa using joined.trans simulated⟩

omit [Fintype I] [Fintype Γ] in
/-- The same bound when the input is supplied on the physical unary index tape. -/
theorem unaryBlockMachine_timeBound (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks Unit Γ) (n : ℕ)
    (last : TM0.Cfg Γ Q) (t : ℕ)
    (execution : StateTransition.EvalsToInTime (TM0.step program)
      (TM0.init (blocks.word (List.replicate n ()))) (some last) t)
    (halted : program last.q last.Tape.head = none) :
    (unaryBlockMachine program control alphabet blocks).TimeBound (generatorData n)
      (2 * (blocks.word (List.replicate n ())).length + 2 * n + 5 + t) := by
  have bound := unarySwap_timeBound (blockMachine program control alphabet blocks)
    (decisionData (List.replicate n ())) _
    (blockMachine_timeBound program control alphabet blocks (List.replicate n ()) last t execution halted)
  simpa only [unaryBlockMachine, unarySwap_decisionData, List.length_replicate] using bound

end

end ComplexityOfGenerators.Simulation
