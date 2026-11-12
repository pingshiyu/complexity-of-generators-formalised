import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Path
import ComplexityOfGenerators.Simulation.WordStack.NoEmission

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

private theorem erased_eq (m : Memory (Cell M) Unit 80) (empty : m.output=[]) :
    m.filterMapOutput (fun _=>none : Unit→Option Unit)=m := by
  apply WordStack.Configuration.ext <;> try rfl
  simp [Memory.filterMapOutput,empty]

theorem prelude_of_runs {n random first second : ℕ} {bits : BitString}
    {after : Memory (Cell M) Unit 80}
    (bootRun : (boot M).Runs n bits (initialMemory M random) first (.done (readyMemory M n random)))
    (pathRun : (pathRetry M p).Runs n bits (readyMemory M n random) second (.done after))
    (empty : after.output=[]) :
    (prelude M p).Runs n bits (initialMemory M random) (first+1+second) (.done after) := by
  have combined := Command.Runs.seq _ _ _ _ _ _ _ bootRun pathRun
  have erased := combined.filterMapOutput (fun _=>none : Unit→Option Unit)
  simpa only [prelude,Result.filterMapOutput,erased_eq M after empty,
    erased_eq M (initialMemory M random) rfl] using erased

theorem prelude_of_exhausted {n random first second : ℕ} {bits : BitString}
    (bootRun : (boot M).Runs n bits (initialMemory M random) first (.done (readyMemory M n random)))
    (pathRun : (pathRetry M p).Runs n bits (readyMemory M n random) second .exhausted) :
    (prelude M p).Runs n bits (initialMemory M random) (first+1+second) .exhausted := by
  have combined := Command.Runs.seq _ _ _ _ _ _ _ bootRun pathRun
  have erased := combined.filterMapOutput (fun _=>none : Unit→Option Unit)
  simpa only [prelude,Result.filterMapOutput,erased_eq M (initialMemory M random) rfl] using erased

theorem prelude_outputFree : Command.OutputFree (prelude M p) := Command.outputFree_erased _

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
