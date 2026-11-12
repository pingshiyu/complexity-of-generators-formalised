import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.ProgramTrace
import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Execution

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pathRetry
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

theorem events_eventReturns (n : ℕ) (bits : BitString) (parts : List ℕ)
    (m : Memory (Cell M) Unit 80) (budget : ℕ) (origin : m.indexHead=0)
    (path : m.store 31=pathWord M parts) (sizes : StoreBound m.store budget)
    (positive : ∀ j∈parts,0<j) :
    ∃ next, ((events M).program 0).EventReturns 0 71 (factorSymbol M) allowed n bits
        (parts.map (fun j=>((),j))) m next ∧
      next.randomHead=m.randomHead ∧ next.output=m.output++List.replicate parts.length () := by
  obtain ⟨_,_,next,_,_,random,output,_,_,_,trace⟩ := events_runs M n bits parts m budget origin path sizes
  have cleanPath : (m.set 0 []).store 31=pathWord M parts := by simpa [Memory.set] using path
  have loopReturn := trace.eventReturns M origin cleanPath positive
  have cleared := (Command.clear_runs (n := n) (0 : Fin 80) bits m (by omega)).compiled 0 (by omega)
  refine ⟨next,?_,random,output⟩
  exact loopReturn.sequence_silent_before cleared (by omega) rfl

theorem command_eventReturns_success (n random failures : ℕ) (parts : List ℕ) (bits : BitString)
    (positive : ∀ j∈parts,0<j)
    (enough : random+(failures+1)*StarCertification.width p n≤bits.length)
    (failed : ∀ k<failures, CertifiedStarPhase.value M p n
      ((bits.drop (random+k*StarCertification.width p n)).take (StarCertification.width p n))=none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (random+failures*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts)) :
    ∃ next, ((command M p).program 0).EventReturns 0 71 (factorSymbol M) allowed n bits
        (parts.map (fun j=>((),j))) (initialMemory M random) next ∧
      next.randomHead=random+(failures+1)*StarCertification.width p n ∧
      next.output=List.replicate parts.length () := by
  obtain ⟨_,_,bootRun⟩ := boot_runs M n random bits
  obtain ⟨_,_,after,pathRun,origin,randomHead,empty,path,sizes⟩ :=
    pathRetry_runs_success M p n random failures parts bits enough failed success
  obtain ⟨next,eventReturn,nextRandom,nextOutput⟩ := events_eventReturns M n bits parts after
    (CertifiedStarPhase.cap p n) origin path sizes positive
  have prefixRun := prelude_of_runs M p bootRun pathRun empty
  have prefixReturn := prefixRun.compiled 0 (by simp [initialMemory])
  refine ⟨next,?_,nextRandom.trans randomHead,?_⟩
  · unfold command
    exact eventReturn.sequence_silent_before prefixReturn (by simp [initialMemory]) empty
  · simpa only [empty,List.nil_append] using nextOutput

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
