import ComplexityOfGenerators.Examples.SATNative.InverseNative.Transform
import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Check
import ComplexityOfGenerators.Examples.SATNative.SubstitutionOutput
import ComplexityOfGenerators.Simulation.WordStack.RandomInput
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

/-! The actual finite SAT inverse controller. Ordinary and auxiliary inputs
are first capped by the generic native loader. The controller checks exact
size, classifies the one-symbol label, and samples one mask bit per input byte. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack

noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 35
abbrev Memory := Simulation.WordStack.Memory Symbol Symbol 35
abbrev Code := Command Symbol Symbol 35
abbrev Step := Routine Symbol Symbol 35

abbrev slots : Fin 32 ↪ Fin 35 := BaseSampler.verifierSlots

def inputRoutine : Step :=
  (Routine.transfer 0 2 (by decide) id).seq
    ((Routine.transfer 1 3 (by decide) id).seq
      (Routine.assign 2 34 33 (by decide) (by decide) (by decide) id))

def sizeSlots : LengthTest.Layout 35 := ⟨![34,32,33,27,28,29], by decide⟩

def sizeTest : Step := LengthTest.routine sizeSlots .one

def parse : Step := (NativeSubstitution.prepareStream (O := Symbol)).rename slots

def moreRoutine : Step :=
  (Routine.assign 4 27 9 (by decide) (by decide) (by decide) id).seq
    ((Routine.assign 10 28 9 (by decide) (by decide) (by decide) id).seq
      ((Routine.clear 29).seq (DrainPair.routine 28 27 29 (by decide) (by decide))))

def maskClock : Step := Routine.assign 32 33 30 (by decide) (by decide) (by decide) id

def orientMask : Step := Routine.transfer 30 31 (by decide) id

def prepareMask : Code :=
  (Routine.clear (O := Symbol) 31).command.seq
    (maskClock.command.seq ((Command.collect 33 30 bitSymbol).seq orientMask.command))

def transform (bit : Bool) : Step := (bodyTransform (O := Symbol) bit).rename slots

def emitSaved : Code := Command.emitWord 34 some

def finishBit (bit : Bool) : Code :=
  prepareMask.seq ((transform bit).command.seq (NativeSubstitution.emitBuffer.rename slots))

def moreBit (bit : Bool) : Code :=
  moreRoutine.command.seq (.branch 27 fun remaining => if remaining.1.isSome then finishBit bit else .drain)

def chooseBit (bit : Bool) : Code :=
  (Command.pop 3).seq (.branch 3 fun tail => if tail.1.isSome then .drain else moreBit bit)

def selectLabel : Code := .branch 3 fun label => match label.1 with
  | none => .branch 10 fun active => if active.1.isSome then .drain else emitSaved
  | some .zero => chooseBit false
  | some .one => chooseBit true
  | _ => .drain

def afterSize : Code := .branch 33 fun equal => if equal.1.isSome then parse.command.seq selectLabel else .drain

def command : Code :=
  (Command.loadIndex 32 .zero).seq (inputRoutine.command.seq (sizeTest.command.seq afterSize))

def program : Program command.Control Symbol Symbol 35 := command.program 0

noncomputable def machine : Machine Symbol Symbol Symbol :=
  InputBank.Capped.controllerMachine program 0 1 id id

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
