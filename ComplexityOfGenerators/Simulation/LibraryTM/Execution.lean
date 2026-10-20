import ComplexityOfGenerators.Simulation.LibraryTM.Loading
import Complexitylib.Models.TuringMachine.Internal

/-! Whole source executions reuse a fixed region, independent of their length.
The final output head is rewound to read the library's verdict in cell one. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM

open TransducerBank
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (M : Complexity.TM n) (word : BitString) (bits : BitString)

def radius (length space tapes : ℕ) : ℕ := 2 * (length + space + tapes + 4)

theorem reachable_markers {c : Complexity.Cfg n M.Q} (path : M.reaches (M.initCfg word) c) :
    ∀ i, (tapes M c i).cells 0 = .start := by
  have invariant : c.input.StartInvariant ∧ (∀ i, (c.work i).StartInvariant) ∧ c.output.StartInvariant := by
    induction path with
    | refl => exact ⟨Complexity.Tape.StartInvariant.init_ofBool word,
        fun _ => Complexity.Tape.StartInvariant.init_nil, Complexity.Tape.StartInvariant.init_nil⟩
    | tail path step ih => exact Complexity.Tape.StartInvariant.step M step ih.1 ih.2.1 ih.2.2
  intro i
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
  · exact invariant.1.1
  · simpa [tapes, -Fin.succ_last] using invariant.2.2.1
  · simpa [tapes] using (invariant.2.1 j).1

theorem configuration_bounded (c : Complexity.Cfg n M.Q) (s : ℕ)
    (space : c.WithinDecisionSpace word.length s) :
    (bank M).Bounded (decisionData word) (word.length + s + 1) (configuration M word c) := by
  refine ⟨le_rfl, Nat.zero_le _, Nat.zero_le _, ?_⟩
  intro j
  simp only [configuration, encoded, Int.natAbs_natCast]
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun i => ?_) j) j
  · exact space.1.2
  · simp only [tapes, Fin.cases_succ, Fin.lastCases_last]
    have := space.2; omega
  · simp only [tapes, Fin.cases_succ, Fin.lastCases_castSucc]
    have := space.1.1 i; omega

theorem reaches_inRegion (s : ℕ)
    (space : ∀ c, M.reaches (M.initCfg word) c → c.WithinDecisionSpace word.length s)
    (finish : Complexity.Cfg n M.Q) (path : M.reaches (M.initCfg word) finish) :
    ∃ ticks, (bank M).RegionSteps (decisionData word) bits (radius word.length s n)
      (configuration M word (M.initCfg word)) ticks (configuration M word finish) := by
  induction path with
  | refl =>
      exact ⟨0, .refl _ ((configuration_bounded M word _ s (space _ .refl)).mono _ (by unfold radius; omega))⟩
  | @tail c d path step ih =>
      obtain ⟨ticks, first⟩ := ih
      have one := (step_schedule M word bits c d step (reachable_markers M word path)).inRegion (bank M)
        (word.length + s + 1) (configuration_bounded M word c s (space c path))
      exact ⟨ticks + (2 * (n + 2) + 2), first.trans (bank M)
        (one.mono (bank M) (by unfold radius; omega))⟩

theorem verdict_run (c : Complexity.Cfg n M.Q) (halted : M.halted c) (s : ℕ)
    (space : c.WithinDecisionSpace word.length s) :
    (bank M).RegionRun (decisionData word) bits (radius word.length s n) (configuration M word c)
      (if c.output.cells 1 = .one then .accepted [] else .rejected) := by
  let j : Fin (n + 2) := (Fin.last n).succ
  let start := encoded M word .verdictOrigin (tapes M c)
  let middle : Config M := {start with state := .verdictStep, head := Function.update start.head j 0}
  let finish : Config M := {middle with state := .verdict, head := Function.update middle.head j 1}
  have go : (bank M).Steps (decisionData word) bits (configuration M word c) 1 start := by
    apply encoded_go
    simp [TapeBank.instruction, bank, transition, encoded, ready, halted, Complexity.TM.halted,
      Complexity.Cfg.isHalted] at *
  have rewind := TapeBank.rewind_steps (bank M) (decisionData word) bits .verdictOrigin .verdictStep
    j rfl (by intros; rfl) c.output.head start rfl (by simp [start, encoded, tapes, j, -Fin.succ_last])
    le_rfl (Nat.zero_le _) (Nat.zero_le _)
  have right : (bank M).Steps (decisionData word) bits middle 1 finish := by
    have path := TapeBank.Steps.read (bank M) (decisionData word) bits middle .verdict .right j rfl
      le_rfl (Nat.zero_le _) (Nat.zero_le _) (by rfl)
    simpa [finish, middle, Move.onInt] using path
  have terminal : (bank M).Executes (decisionData word) bits finish 0
      (if c.output.cells 1 = .one then .accepted [] else .rejected) := by
    by_cases yes : c.output.cells 1 = .one
    · rw [ite_eq_left yes]
      apply TapeBank.Executes.accept
      simp [TapeBank.instruction, bank, transition, finish, middle, start, encoded, select,
        tapes, j, image, yes, -Fin.succ_last]
    · rw [ite_eq_right yes]
      apply TapeBank.Executes.reject
      simp [TapeBank.instruction, bank, transition, finish, middle, start, encoded, select,
        tapes, j, image, yes, -Fin.succ_last]
  have run := ((go.trans (bank M) rewind).trans (bank M) right).executes (bank M) terminal
  exact (run.inRegion (bank M) (configuration_bounded M word c s space)).mono (bank M)
    (by have := space.2; unfold radius; omega)

theorem run_inRegion (s : ℕ)
    (space : ∀ c, M.reaches (M.initCfg word) c → c.WithinDecisionSpace word.length s)
    (finish : Complexity.Cfg n M.Q) (path : M.reaches (M.initCfg word) finish) (halted : M.halted finish) :
    (bank M).RegionRun (decisionData word) bits (radius word.length s n) (bank M).initialConfiguration
      (if finish.output.cells 1 = .one then .accepted [] else .rejected) := by
  obtain ⟨ticks, simulation⟩ := reaches_inRegion M word bits s space finish path
  have loader := ((load_initial M bits word).inRegion (bank M) 0 ((bank M).initial_bounded _)).mono
    (bank M) (by unfold radius; omega : 0 + (2 * word.length + 4) ≤ radius word.length s n)
  exact ((verdict_run M word bits finish halted s (space finish path)).prepend (bank M) simulation).prepend
    (bank M) loader

end ComplexityOfGenerators.Simulation.LibraryTM
