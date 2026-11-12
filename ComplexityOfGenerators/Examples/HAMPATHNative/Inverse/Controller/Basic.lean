import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Correctness
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Output.Correctness
import ComplexityOfGenerators.Simulation.WordStack.CollectForward
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Output.Store
abbrev Memory := Simulation.WordStack.Memory Symbol Symbol 64

def input : Routine Symbol Symbol 64 :=
  (Routine.clearMany [32,33]).seq
    ((Routine.transfer 0 32 (by decide) id).seq (Routine.transfer 1 33 (by decide) id))

def emit (source : Fin 64) : Command Symbol Symbol 64 := Command.emitWord source some

noncomputable def finish : Command Symbol Symbol 64 :=
  .branch 41 fun state => if state.1.isSome then Output.routine.command.seq (emit 31) else .drain

noncomputable def randomPhase : Command Symbol Symbol 64 :=
  Choose.sampleClock.command.seq
    ((Command.collectForward 46 42 47 (by decide) Symbol.bit).seq
      (Choose.routine.command.seq finish))

noncomputable def dispatch : Command Symbol Symbol 64 :=
  .branch 41 fun state => if state.1.isSome then
    .branch 33 fun label => if label.1.isNone then emit 32 else randomPhase
  else .drain

noncomputable def command : Command Symbol Symbol 64 :=
  (Command.loadIndex 34 (.bit true)).seq
    (input.command.seq (Classify.routine.command.seq dispatch))

noncomputable def program := command.program 63

noncomputable def machine : Machine Symbol Symbol Symbol :=
  InputBank.Capped.controllerMachine program 0 1 id id

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
