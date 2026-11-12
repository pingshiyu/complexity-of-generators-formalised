import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Loop
import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Parameters

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

theorem boot_runs (n random : ℕ) (bits : BitString) :
    ∃ ticks≤100*(n+1), (boot M).Runs n bits (initialMemory M random) ticks
      (.done (readyMemory M n random)) := by
  obtain ⟨ticks,bound,run⟩ := ExpectedStarGenerator.boot_runs M emptyPhase n random bits
  exact ⟨ticks,bound,run.mapOutput (fun _=>())⟩

theorem ready_bound (n random : ℕ) : StoreBound (readyMemory M n random).store n := by
  intro k
  by_cases first : k=13 <;> by_cases second : k=22 <;>
    simp [readyMemory,Memory.mapOutput,ExpectedStarGenerator.readyMemory,
      ExpectedStarGenerator.readyStore,first,second]

theorem pathRetry_runs_success (n random failures : ℕ) (parts : List ℕ) (bits : BitString)
    (enough : random+(failures+1)*StarCertification.width p n≤bits.length)
    (failed : ∀ k<failures, CertifiedStarPhase.value M p n
      ((bits.drop (random+k*StarCertification.width p n)).take (StarCertification.width p n))=none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (random+failures*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts)) :
    ∃ ticks≤(failures+1)*ExpectedStarGenerator.pathCallBudget M p n, ∃ next,
      (pathRetry M p).Runs n bits (readyMemory M n random) ticks (.done next) ∧
      next.indexHead=0 ∧ next.randomHead=random+(failures+1)*StarCertification.width p n ∧
      next.output=[] ∧ next.store 31=pathWord M parts ∧
      StoreBound next.store (CertifiedStarPhase.cap p n) := by
  have sizes : StoreBound (ExpectedStarGenerator.readyMemory M emptyPhase n random).store
      (CertifiedStarPhase.cap p n) :=
    (ready_bound M n random).mono (by have := ExpectedStarGenerator.outer_indexBudget p n; omega)
  obtain ⟨ticks,bound,after,run,origin,randomHead,output,path,_,sizesAfter⟩ :=
    ExpectedStarGenerator.pathRetry_runs_success M p emptyPhase n failures parts bits
      (ExpectedStarGenerator.readyMemory M emptyPhase n random) rfl rfl
      (ExpectedStarGenerator.ready_owned M emptyPhase n random) sizes enough failed success
  refine ⟨ticks,bound,after.mapOutput (fun _=>()),run.mapOutput (fun _=>()),origin,randomHead,?_,path,sizesAfter⟩
  simp [Memory.mapOutput,output]

def PathResult (n : ℕ) : Result (Cell M) Unit 80 → Prop
  | .exhausted => True
  | .done after => after.indexHead=0 ∧ after.output=[] ∧
      StoreBound after.store (CertifiedStarPhase.cap p n) ∧ ∃ parts : List ℕ,
        parts.sum=n ∧ (∀ j∈parts,0<j) ∧ after.store 31=pathWord M parts ∧
        ExpectedStarGenerator.PathHit M p n

theorem pathRetry_runs_total (n random : ℕ) (bits : BitString) :
    ∃ ticks result, (pathRetry M p).Runs n bits (readyMemory M n random) ticks result ∧
      PathResult M p n result := by
  have sizes : StoreBound (ExpectedStarGenerator.readyMemory M emptyPhase n random).store
      (CertifiedStarPhase.cap p n) :=
    (ready_bound M n random).mono (by have := ExpectedStarGenerator.outer_indexBudget p n; omega)
  obtain ⟨ticks,result,run,post,hit⟩ := ExpectedStarGenerator.pathRetry_runs_total_with_hit M p emptyPhase n bits
    (ExpectedStarGenerator.readyMemory M emptyPhase n random) rfl rfl
    (ExpectedStarGenerator.ready_owned M emptyPhase n random) sizes
  cases result with
  | exhausted => exact ⟨ticks,.exhausted,run.mapOutput (fun _=>()),trivial⟩
  | done after =>
      obtain ⟨origin,empty,_,sizesAfter,parts,total,positive,path⟩ := post
      refine ⟨ticks,.done (after.mapOutput (fun _=>())),run.mapOutput (fun _=>()),origin,?_,sizesAfter,
        parts,total,positive,path,hit⟩
      simp [Memory.mapOutput,empty]

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
