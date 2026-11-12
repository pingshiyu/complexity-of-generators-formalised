import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Trace
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses

/-! Lucky source records share a finite native execution and retain its
first-moment budget; the records' words are never capped or buffered. -/
namespace ComplexityOfGenerators.Simulation.OriginalStarGenerator
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

include expected in
theorem runs_records (n : ℕ) (parts : List ℕ) (records : List OriginalSourceFamilySampler.Record)
    (available : CertifiedStarPhase.AvailableComposition G n parts)
    (requests : records.map OriginalSourceFamilySampler.request=parts.map (fun j=>(false,j)))
    (minimal : ∀ record∈records,OriginalSourceFamilySampler.MinimalRecord (ExpectedOriginalStarSampling.families G) record) :
    ∃ bits ticks,bits≠[] ∧
      ticks≤25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2+
        (6*n+20)*(OriginalSourceFamilySampler.totalTime (ExpectedOriginalStarSampling.families G) records+records.length) ∧
      (machine G.machine p).run (generatorData n) bits ticks=
        .halted (.accepted (OriginalSourceFamilySampler.words (ExpectedOriginalStarSampling.families G) records)) := by
  obtain ⟨outer,outerLength,outerHit⟩ := CertifiedStarPhase.value_full_support G p n parts available expected
  let bits := outer++OriginalSourceFamilySampler.seedWord records
  have sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace (ExpectedOriginalStarSampling.families G)
      bits (StarCertification.width p n) (parts.map (fun j=>(false,j))) records := by
    have actual := OriginalSourceFamilySampler.records_finiteTrace (ExpectedOriginalStarSampling.families G)
      records minimal outer []
    simpa only [List.append_nil,outerLength,requests] using actual
  have taken : bits.take (StarCertification.width p n)=outer := by
    dsimp only [bits]
    rw [←outerLength,List.take_left]
  have enough : (0+1)*StarCertification.width p n≤bits.length := by
    simp only [Nat.zero_add,Nat.one_mul,bits,List.length_append,outerLength]
    omega
  obtain ⟨ticks,bound,run⟩ := machine_runs_trace G p n 0 parts records bits available.1
    (fun j member=>(available.2 j member).1) enough (by intro k before;omega)
    (by simpa only [Nat.zero_mul,List.drop_zero,taken] using outerHit)
    (by simpa only [Nat.zero_add,Nat.one_mul] using sourceTrace)
  have nonempty : bits≠[] := by
    intro empty
    have length := congrArg List.length empty
    simp only [bits,List.length_append,outerLength,List.length_nil] at length
    have positive := (StarCertification.width p).positive n
    omega
  exact ⟨bits,ticks,nonempty,by simpa only [Nat.zero_add,Nat.one_pow,Nat.mul_one] using bound,run⟩

end
end ComplexityOfGenerators.Simulation.OriginalStarGenerator
