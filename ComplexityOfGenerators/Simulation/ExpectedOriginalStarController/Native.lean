import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Execution
import ComplexityOfGenerators.Simulation.WordStack.UnaryExport
import ComplexityOfGenerators.Proofs.FixedBlockRetryCriteria

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

noncomputable def program : Program (command M p).Control (Cell M) Unit 80 := (command M p).program 0

noncomputable def alphabetFintype : Fintype (Cell M) := inferInstance
attribute [irreducible] alphabetFintype

noncomputable def controlFintype : Fintype (command M p).Control := by
  letI := alphabetFintype M
  exact Command.controlFintype (command M p)
attribute [irreducible] controlFintype

noncomputable def machine : Machine Unit Bool Unit := by
  letI := alphabetFintype M
  letI := controlFintype M p
  exact (program M p).machine

/-- The native hook reads the shared origin or an occupied export-stack cell.
Its positive-factor interface is proved from actual bank memory below. -/
def parameter (_event : Unit) (raw : Option (Fin (machine M p).symbols)) : Bool := by
  letI := alphabetFintype M
  letI := controlFintype M p
  exact unaryExport (program M p).bank 71 raw

theorem compile_run {n ticks : ℕ} {bits : BitString} {result : Outcome Unit}
    (execution : (program M p).Executes n bits (program M p).initialConfiguration ticks result) :
    ∃ nativeTicks≤1+(2*ticks+1)*(4*ticks+4),
      (machine M p).run (generatorData n) bits nativeTicks = .halted result := by
  letI := alphabetFintype M
  letI := controlFintype M p
  exact (program M p).run_compiled execution

theorem machine_execution (n : ℕ) (bits : BitString) :
    ∃ ticks result, (machine M p).run (generatorData n) bits ticks=.halted result.outcome ∧
      GeneratedResult M n result := by
  obtain ⟨stackTicks,result,run,post⟩ := command_runs_total M p n 0 bits
  obtain ⟨ticks,_,native⟩ := compile_run M p (run.executes 0)
  exact ⟨ticks,result,native,post⟩

theorem machine_halting (n : ℕ) (bits : BitString) : (machine M p).Halts (generatorData n) bits := by
  obtain ⟨ticks,result,run,_⟩ := machine_execution M p n bits
  exact ⟨ticks,result.outcome,run⟩

theorem machine_runs_success (n failures : ℕ) (parts : List ℕ) (bits : BitString)
    (total : parts.sum=n) (positive : ∀ j∈parts,0<j)
    (enough : (failures+1)*StarCertification.width p n≤bits.length)
    (failed : ∀ k<failures, CertifiedStarPhase.value M p n
      ((bits.drop (k*StarCertification.width p n)).take (StarCertification.width p n))=none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (failures*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts)) :
    ∃ ticks≤25*(primitiveCoefficient M p n)^2*(failures+1)^2,
      (machine M p).run (generatorData n) bits ticks=
        .halted (.accepted (List.replicate parts.length ())) := by
  obtain ⟨stackTicks,bound,next,run,output,_,_,_⟩ := command_runs_success M p n 0 failures parts bits
    total positive (by simpa using enough) (by simpa using failed) (by simpa using success)
  obtain ⟨ticks,compiler,native⟩ := compile_run M p (run.executes 0)
  have budget := Machine.retry_compiler_cost_le stackTicks (primitiveCoefficient M p n) failures
    ((primitiveCoefficient M p).positive n) bound
  exact ⟨ticks,compiler.trans budget,by simpa only [Result.outcome,output] using native⟩

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
