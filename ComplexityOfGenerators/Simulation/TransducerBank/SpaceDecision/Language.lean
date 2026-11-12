import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Support
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns.Semantics

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision

open BinaryCounter Multitape.SpaceConfigurations
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I O QB SB : Type} {m : ℕ} [Fintype QB] [Fintype SB]

/-- Clock construction followed by clocked source execution preserves the
nondeterministic language. The finite configuration bound supplies an actual
short accepting seed; the clock coefficient is fixed before execution. -/
theorem accepted_iff {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)
    (source : TapeBank I Bool O QB SB m) (copies : ℕ) (word : List I) (base : ℕ)
    (bounded : source.SpaceBound (decisionData word) base)
    (termination : ∀ choices,∃ ticks result,source.Executes (decisionData word) choices source.initialConfiguration ticks result)
    (enough : clockWidth (Q:=QB) (S:=SourceSymbol constructor.machine.Work SB)
      (k:=m+(constructor.machine.tapes+1)) word.length (sourceRadius constructor base word.length)≤
        BinaryClockInitialisation.width (space:=space) copies word.length) :
    (∃ choices ticks result,(bank constructor.machine.program source copies).Executes (decisionData word) choices
      (bank constructor.machine.program source copies).initialConfiguration ticks (.accepted result)) ↔
      ∃ choices ticks result,source.Executes (decisionData word) choices source.initialConfiguration ticks (.accepted result) := by
  obtain ⟨prefixTicks,ctor,heads,support,preparation⟩ := prepared_steps constructor source copies (decisionData word)
  let radius := sourceRadius constructor base word.length
  let digits := BinaryClock.powerDigits (BinaryClockInitialisation.width (space:=space) copies word.length)
  have baseRoom : base≤radius := by dsimp [radius,sourceRadius];omega
  have ctorRoom : constructor.constant*(space word.length+1)≤radius := by dsimp [radius,sourceRadius];omega
  have logRoom : Nat.clog 2 (word.length+1)≤radius := by dsimp [radius,sourceRadius];omega
  have heads' : ∀ tape,(ctor.head tape).natAbs≤radius := fun tape => (heads tape).trans ctorRoom
  have space' : source.SpaceBound (decisionData word) radius := fun bits ticks finish path =>
    (bounded bits ticks finish path).mono source baseRoom
  have allBound := source_future_bound constructor.machine.program source (decisionData word) word.length radius ctor heads' space' termination
  have clockLaw (choices : BitString) (result : List O) :
      (∃ ticks,(bank constructor.machine.program source copies).Executes (decisionData word) choices
        (bank constructor.machine.program source copies).initialConfiguration ticks (.accepted result)) ↔
      ∃ ticks,ticks<FixedBitBlocks.decode digits ∧ (sourceBank constructor.machine.program source).Executes (decisionData word) choices
        (sourceConfiguration constructor.machine.program source word.length ctor) ticks (.accepted result) := by
    exact prefix_accepted_iff constructor.machine.program source copies word.length digits (BinaryClock.powerDigits_canonical _) ctor
      (decisionData word) choices radius prefixTicks (allBound choices) ((preparation choices).toSteps _) result
  constructor
  · rintro ⟨choices,ticks,result,accepted⟩
    obtain ⟨time,small,sourceAccepted⟩ := (clockLaw choices result).mp ⟨ticks,accepted⟩
    obtain ⟨sourceTime,run⟩ := (source_accepted_iff constructor.machine.program source (decisionData word) choices word.length radius ctor heads' space'
      result (termination choices)).mp ⟨time,sourceAccepted⟩
    exact ⟨choices,sourceTime,result,run⟩
  · rintro ⟨choices,ticks,result,accepted⟩
    obtain ⟨time,embedded⟩ := (source_accepted_iff constructor.machine.program source (decisionData word) choices word.length radius ctor heads' space'
      result (termination choices)).mpr ⟨ticks,accepted⟩
    have valid := source_valid constructor.machine.program source word.length ctor (constructor.constant*(space word.length+1)) radius
      heads support ctorRoom logRoom
    obtain ⟨shortChoices,shortTime,shortResult,small,shortRun⟩ := SpaceShortRuns.short_accepting_run_from
      (sourceBank constructor.machine.program source) word choices radius embedded valid (allBound choices)
    have restored : (SpaceShortRuns.snapshot (sourceConfiguration constructor.machine.program source word.length ctor)).restore 0 ([] : List O)=
        sourceConfiguration constructor.machine.program source word.length ctor := rfl
    rw [restored] at shortRun
    have shortBudget : shortTime<FixedBitBlocks.decode digits := by
      have power := Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) enough
      simpa only [digits,BinaryClock.powerDigits_value] using small.trans_le power
    obtain ⟨nativeTime,nativeRun⟩ := (clockLaw shortChoices shortResult).mpr ⟨shortTime,shortBudget,shortRun⟩
    exact ⟨shortChoices,nativeTime,shortResult,nativeRun⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
