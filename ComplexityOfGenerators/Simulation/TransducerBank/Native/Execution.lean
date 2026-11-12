import ComplexityOfGenerators.Simulation.TransducerBank.Native.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.Native

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

/-- Every native transcript is replayed transition for transition by one bank. -/
theorem transcript_executes {data : InputData I A} {bits : BitString}
    {source : Configuration M} {log : BitString} {result : Outcome O}
    (recorded : M.ExecutionTranscript data bits source log result) :
    (bank M).Executes data bits (configuration M source) log.length result := by
  induction recorded with
  | halt source result terminal =>
    cases action : M.transition source.state data.input[source.inputHead]?
        data.auxiliary[source.auxiliaryHead]?
        (if source.indexHead < data.index then some () else none)
        (source.work source.workHead) with
    | accept =>
        have same : result = .accepted source.output := by
          simpa [Machine.observe, action] using terminal.symm
        subst result
        exact .accept _ (by simp only [TapeBank.instruction, bank, configuration]; rw [action])
    | reject =>
        have same : result = .rejected := by
          simpa [Machine.observe, action] using terminal.symm
        subst result
        exact .reject _ (by simp only [TapeBank.instruction, bank, configuration]; rw [action])
    | step next write work input auxiliary index emit =>
        simp [Machine.observe, action] at terminal
    | readRandom no yes =>
        have ended : ¬ source.randomHead < bits.length := by
          intro live
          simp [Machine.observe, action, live] at terminal
        have absent : bits[source.randomHead]? = none :=
          List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt ended)
        have same : result = .exhausted := by
          simpa [Machine.observe, action, ended] using terminal.symm
        subst result
        exact .exhausted _ no yes
          (by simp only [TapeBank.instruction, bank, configuration]; rw [action]) absent
  | step source tail result next write work input auxiliary index emit action rest ih =>
      apply TapeBank.Executes.step _ next (write.or (source.work source.workHead))
        work input auxiliary index emit tail.length result
        (by simp only [TapeBank.instruction, bank, configuration]; rw [action])
      rw [← configuration_step]
      exact ih
  | random source bit tail result no yes action lookup rest ih =>
      apply TapeBank.Executes.random _ no yes bit tail.length result
        (by simp only [TapeBank.instruction, bank, configuration]; rw [action]) lookup
      simpa only [← configuration_random] using ih

/-- A bounded native run yields a bank execution within the identical bound. -/
theorem executes_of_run (data : InputData I A) (bits : BitString)
    (source : Configuration M) (ticks : ℕ) (result : Outcome O)
    (run : M.runFrom data bits source ticks = .halted result) :
    ∃ bankTicks, bankTicks ≤ ticks ∧
      (bank M).Executes data bits (configuration M source) bankTicks result := by
  obtain ⟨log, small, recorded⟩ := M.executionTranscript_of_runFrom data bits source ticks result run
  exact ⟨log.length, small, transcript_executes M recorded⟩

theorem timeBound (data : InputData I A) (ticks : ℕ) (bounded : M.TimeBound data ticks) :
    (machine M).TimeBound data ticks := by
  intro bits
  obtain ⟨result, run⟩ := bounded bits
  rw [← M.runFrom_initial] at run
  obtain ⟨bankTicks, small, execution⟩ :=
    executes_of_run M data bits M.initialConfiguration ticks result run
  exact ⟨bankTicks, result, small, execution⟩

end ComplexityOfGenerators.Simulation.TransducerBank.Native
