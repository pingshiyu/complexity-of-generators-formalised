import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- A complete region execution bounds every reachable prefix on the same
finite random tape. The bank table fixes the path once that tape is fixed. -/
theorem RegionSteps.bounds_prefix {data : InputData I A} {bits : BitString} {radius time ticks : ℕ}
    {source finish target : BankConfiguration O Q S k} {result : Outcome O}
    (path : B.RegionSteps data bits radius source time finish)
    (terminal : B.Executes data bits finish 0 result) (reached : B.Steps data bits source ticks target) :
    B.Bounded data radius target := by
  induction path generalizing ticks target with
  | refl source bounded => cases terminal <;> cases reached <;> simp_all
  | random source no yes bit time finish bounded table lookup rest ih =>
      cases reached with
      | refl => exact bounded
      | random _ no' yes' bit' ticks target table' lookup' tail =>
          have controls : no'=no ∧ yes'=yes := by simp_all
          obtain ⟨rfl,rfl⟩ := controls
          have same : bit'=bit := by simp_all
          subst bit'
          exact ih terminal tail
      | step _ _ _ _ _ _ _ _ _ _ table' _ => simp_all
  | step source next write work input auxiliary index emit time finish bounded table rest ih =>
      cases reached with
      | refl => exact bounded
      | random _ _ _ _ _ _ table' _ _ => simp_all
      | step _ next' write' work' input' auxiliary' index' emit' ticks target table' tail =>
          have same : next'=next ∧ write'=write ∧ work'=work ∧ input'=input ∧
              auxiliary'=auxiliary ∧ index'=index ∧ emit'=emit := by simp_all
          obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := same
          exact ih terminal tail

theorem RegionRun.bounds_prefix {data : InputData I A} {bits : BitString} {radius ticks : ℕ}
    {source target : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.RegionRun data bits radius source result) (reached : B.Steps data bits source ticks target) :
    B.Bounded data radius target := by
  obtain ⟨time,finish,path,terminal⟩ := run
  exact path.bounds_prefix B terminal reached

theorem spaceBound_of_regionRuns (data : InputData I A) (radius : ℕ)
    (runs : ∀ bits, ∃ result, B.RegionRun data bits radius B.initialConfiguration result) :
    B.SpaceBound data radius := by
  intro bits ticks target reached
  obtain ⟨result,run⟩ := runs bits
  exact run.bounds_prefix B reached

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
