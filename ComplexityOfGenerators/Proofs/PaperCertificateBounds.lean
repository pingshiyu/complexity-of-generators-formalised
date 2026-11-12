import ComplexityOfGenerators.Proofs.AcceptingTimeGeneration

/-! Productive accepting-time bounds already control every finite random
seed; this fact applies to arbitrary ordinary and auxiliary input data. -/
namespace ComplexityOfGenerators.Machine
variable {I A O : Type} (M : Machine I A O)

theorem accepting_timeBound_of_nonempty (data : InputData I A) (time : ℕ)
    (generator : M.IsGenerator data) (bounded : M.AcceptingTimeBound data time)
    (nonempty : (M.generatedLanguage data).Nonempty) : M.TimeBound data time := by
  intro bits
  cases original : M.run data bits time with
  | halted result => exact ⟨result,original⟩
  | running state =>
      let extra := List.replicate (time+1) false
      obtain ⟨word,produced⟩ := M.accepts_long_tape_of_acceptingTimeBound data time generator bounded
        (bits++extra) (by simp [extra];omega) nonempty
      have accepted := bounded (bits++extra) word produced
      rw [M.run_append_of_not_exhausted data bits extra time (by simp [original]),original] at accepted
      cases accepted

theorem generatorTimeBound_acceptingTimeBound (data : InputData I A) (seed time : ℕ)
    (bound : M.GeneratorTimeBound data seed time) : M.AcceptingTimeBound data time := by
  intro bits word produced
  have nonempty : (M.generatedLanguage data).Nonempty :=
    ⟨word,bits++[false],by simp,M.produces_append data bits [false] word produced⟩
  have allTapes := M.generatorTimeBound_timeBound_of_nonempty data seed time bound nonempty
  exact M.produces_at_bound data bits time word (allTapes bits) produced

end ComplexityOfGenerators.Machine
