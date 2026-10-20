import ComplexityOfGenerators.Simulation.LibraryTM.Alphabet.Program

/-! Reuse the binary compiler's complete simulation after input loading. The
external input head remains at its end; virtual heads and space are unchanged. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {n : ℕ} (M : Complexity.TM n)

theorem no_random (full : BitString) (c : LibraryTM.Config M) (no yes : LibraryTM.State M)
    (table : (LibraryTM.bank M).instruction (decisionData full) c = .readRandom no yes) : False := by
  have h := LibraryTM.deterministic M c.state (decisionData full).input[c.inputHead]?
    (decisionData full).auxiliary[c.auxiliaryHead]?
    (if c.indexHead < (decisionData full).index then some () else none)
    (decide (c.head ((LibraryTM.bank M).select c.state) = 0))
    (c.tape ((LibraryTM.bank M).select c.state) (c.head ((LibraryTM.bank M).select c.state)))
  simp only [TapeBank.instruction] at table
  rw [table] at h
  exact h

theorem lift_path (word : List α) (full bits : BitString) {r t : ℕ} {a b : LibraryTM.Config M}
    (path : (LibraryTM.bank M).RegionSteps (decisionData full) bits r a t b)
    (endInput : a.inputHead = full.length) :
    b.inputHead = full.length ∧
      (bank M).RegionSteps (decisionData word) bits r (lift M word a) t (lift M word b) := by
  induction path with
  | refl c bound => exact ⟨endInput, .refl _ (lift_bounded M word full r c bound)⟩
  | random c no yes bit t d bound table lookup rest ih => exact (no_random M full c no yes table).elim
  | step c next write work input auxiliary index emit t d bound table rest ih =>
    have table' := table
    simp only [TapeBank.instruction, LibraryTM.bank, decisionData, endInput, List.getElem?_length] at table'
    have stay := exhausted_stays M c.state _ _ next write work input auxiliary index emit table'
    subst input
    have nextEnd : ((LibraryTM.bank M).advance (decisionData full) c next write work .stay auxiliary index emit).inputHead
        = full.length := by simp [TapeBank.advance, Move.onInput, decisionData, endInput]
    obtain ⟨lastEnd, mapped⟩ := ih nextEnd
    refine ⟨lastEnd, .step _ (.run next) write work .stay auxiliary index emit t _
      (lift_bounded M word full r c bound) ?_ ?_⟩
    · rw [lift_instruction M word full c endInput, table]; rfl
    · rwa [lift_advance]

theorem lift_terminal (word : List α) (full bits : BitString) (c : LibraryTM.Config M)
    (endInput : c.inputHead = full.length) (result : Outcome Unit)
    (terminal : (LibraryTM.bank M).Executes (decisionData full) bits c 0 result) :
    (bank M).Executes (decisionData word) bits (lift M word c) 0 result := by
  cases terminal with
  | accept c table => exact .accept _ (by rw [lift_instruction M word full c endInput, table]; rfl)
  | reject c table => exact .reject _ (by rw [lift_instruction M word full c endInput, table]; rfl)
  | exhausted c no yes table absent => exact (no_random M full c no yes table).elim

theorem lift_run (word : List α) (full bits : BitString) {r : ℕ} {c : LibraryTM.Config M}
    {result : Outcome Unit} (run : (LibraryTM.bank M).RegionRun (decisionData full) bits r c result)
    (endInput : c.inputHead = full.length) :
    (bank M).RegionRun (decisionData word) bits r (lift M word c) result := by
  obtain ⟨ticks, finish, path, terminal⟩ := run
  obtain ⟨lastEnd, mapped⟩ := lift_path M word full bits path endInput
  exact ⟨ticks, lift M word finish, mapped, lift_terminal M word full bits finish lastEnd result terminal⟩

theorem simulated_run (word : List α) (bits : BitString) (s : ℕ)
    (space : ∀ c, M.reaches (M.initCfg (NativeNTM.encode word)) c →
      c.WithinDecisionSpace (NativeNTM.encode word).length s)
    (finish : Complexity.Cfg n M.Q) (path : M.reaches (M.initCfg (NativeNTM.encode word)) finish)
    (halted : M.halted finish) :
    (bank M).RegionRun (decisionData word) bits (radius (NativeNTM.encode word).length s n)
      (lift M word (configuration M (NativeNTM.encode word) (M.initCfg (NativeNTM.encode word))))
      (if finish.output.cells 1 = .one then .accepted [] else .rejected) := by
  obtain ⟨ticks, simulation⟩ := reaches_inRegion M (NativeNTM.encode word) bits s space finish path
  exact lift_run M word (NativeNTM.encode word) bits
    ((verdict_run M (NativeNTM.encode word) bits finish halted s (space finish path)).prepend
      (LibraryTM.bank M) simulation) rfl

end
end ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
