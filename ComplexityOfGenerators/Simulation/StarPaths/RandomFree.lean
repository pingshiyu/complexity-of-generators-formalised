import ComplexityOfGenerators.Simulation.StarPaths.Native
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.StarPaths
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

/-- Path selection consumes the caller's precollected coin stack; no nested
random request is hidden in its parser, DP, validation or fallback routines. -/
theorem pathRoutine_randomFree {O : Type} : (pathRoutine (O := O)).command.RandomFree := by
  simp [pathRoutine,dpRoutine,prepare,outerBody,stageSetup,stageRoutine,appendEntry,stageBody,
    readEntry,consider,capture,saveFallback,proposalRoutine,proposalSetup,proposalFinish,
    proposalLoop,proposalCoin,validationRoutine,validationSetup,validationLoop,validationBody,
    validationFactor,selectResult,WordStack.DrainPair.routine,WordStack.DrainPair.body,apply_ite]

end ComplexityOfGenerators.Simulation.StarPaths
