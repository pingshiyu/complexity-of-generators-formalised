import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem commit_advance (data : InputData I A) (fuel used : ℕ)
    (source : BankConfiguration O Q S k) (next : Q) (write : S)
    (work input auxiliary index : Move) (emit : Option O) :
    (bank B).advance data
      {configuration B fuel used source with state :=
        (.commit (B.select source.state) next write work input auxiliary index emit)}
      (.fetch next) (.inl write) work input auxiliary index emit =
      configuration B fuel used (B.advance data source next write work input auxiliary index emit) := by
  have distinct : Fin.last k ≠ (B.select source.state).castSucc :=
    Ne.symm (Fin.ne_of_lt (B.select source.state).castSucc_lt_last)
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, configuration, bank]
  · funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Function.update_apply, distinct]
    · by_cases same : j = B.select source.state
      · subst j; simp [Function.update_apply]
      · simp [Function.update_apply, same]
  · funext j p
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Function.update_apply, distinct]
    · by_cases same : j = B.select source.state
      · subst j
        by_cases location : p = source.head (B.select source.state) <;>
          simp [Function.update_apply, location]
      · simp [Function.update_apply, same]

theorem clock_step (data : InputData I A) (bits : BitString) (fuel used r : ℕ)
    (source : BankConfiguration O Q S k) (phase next : Phase Q S O k)
    (selected : (bank B).select phase = Fin.last k)
    (bounds : B.Bounded data r source)
    (table : ∀ cell, (bank B).transition phase
      data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some () else none)
      (decide ((used : ℤ) = 0)) cell =
        .step next cell .right .stay .stay .stay none) :
    (bank B).Steps data bits {configuration B fuel used source with state := phase} 1
      {configuration B fuel (used + 1) source with state := next} := by
  have instruction : (bank B).instruction data
      {configuration B fuel used source with state := phase} =
      .step next (clockTape B fuel used) .right .stay .stay .stay none := by
    simp only [TapeBank.instruction, configuration, selected,
      Fin.lastCases_last]
    exact table _
  have step := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
  simpa only [clock_advance B data fuel used source phase next selected
    bounds.input bounds.auxiliary bounds.index] using step

/-- A productive source step uses exactly one physical clock mark and three
finite bank transitions. No source tape is scanned. -/
theorem step_path (data : InputData I A) (bits : BitString) (fuel used r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded data r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O)
    (action : B.instruction data source = .step next write work input auxiliary index emit)
    (live : used < fuel) :
    (bank B).Steps data bits (configuration B fuel used source) 3
      (configuration B fuel (used + 1)
        (B.advance data source next write work input auxiliary index emit)) := by
  let waiting : Phase Q S O k :=
    .tickStep (B.select source.state) next write work input auxiliary index emit
  let committing : Phase Q S O k :=
    .commit (B.select source.state) next write work input auxiliary index emit
  have first : (bank B).Steps data bits (configuration B fuel used source) 1
      {configuration B fuel used source with state := waiting} := by
    apply TapeBank.Steps.go (bank B) data bits _ waiting
      bounds.input bounds.auxiliary bounds.index
    rw [fetch_instruction B data fuel used source, action]
    simp [waiting, configuration, bank]
  have second : (bank B).Steps data bits
      {configuration B fuel used source with state := waiting} 1
      {configuration B fuel (used + 1) source with state := committing} := by
    have instruction : (bank B).instruction data
        {configuration B fuel used source with state := waiting} =
        .step committing (clockTape B fuel used) .right .stay .stay .stay none := by
      simp [TapeBank.instruction, waiting, committing, bank, configuration, clockTape,
        marked, live]
    have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
    simpa only [clock_advance B data fuel used source waiting committing rfl
      bounds.input bounds.auxiliary bounds.index] using actual
  have third : (bank B).Steps data bits
      {configuration B fuel (used + 1) source with state := committing} 1
      (configuration B fuel (used + 1)
        (B.advance data source next write work input auxiliary index emit)) := by
    have instruction : (bank B).instruction data
        {configuration B fuel (used + 1) source with state := committing} =
        .step (.fetch next) (.inl write) work input auxiliary index emit := by
      simp [TapeBank.instruction, committing, bank]
    have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
    simpa only [committing, commit_advance] using actual
  exact (first.trans (bank B) second).trans (bank B) third

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
