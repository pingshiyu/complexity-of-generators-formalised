import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem Steps.inFixedRegion {data : InputData I A} {bits : BitString} {radius ticks : ℕ}
    {start finish : BankConfiguration O Q S k} (path : B.Steps data bits start ticks finish)
    (allBound : ∀ time current, B.Steps data bits start time current → B.Bounded data radius current) :
    B.RegionSteps data bits radius start ticks finish := by
  induction path with
  | refl start => exact .refl _ (allBound 0 start (.refl _))
  | random start no yes bit ticks finish table lookup rest ih =>
    apply RegionSteps.random start no yes bit ticks finish (allBound 0 start (.refl _)) table lookup
    exact ih (fun time current path => allBound (time+1) current (.random start no yes bit time current table lookup path))
  | step start next write work input auxiliary index emit ticks finish table rest ih =>
    apply RegionSteps.step start next write work input auxiliary index emit ticks finish (allBound 0 start (.refl _)) table
    exact ih (fun time current path => allBound (time+1) current (.step start next write work input auxiliary index emit time current table path))

theorem Executes.regionRun_of_prefixBound {data : InputData I A} {bits : BitString} {radius ticks : ℕ}
    {start : BankConfiguration O Q S k} {result : Outcome O} (run : B.Executes data bits start ticks result)
    (allBound : ∀ time current, B.Steps data bits start time current → B.Bounded data radius current) :
    B.RegionRun data bits radius start result := by
  obtain ⟨finish,path,halt⟩ := run.path B
  exact ⟨ticks,finish,path.inFixedRegion B allBound,halt⟩

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
