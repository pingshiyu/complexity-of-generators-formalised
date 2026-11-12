import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Views

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def counted (m : Memory) : Memory :=
  {m with store := Choose.sampleClock.eval m.store}

noncomputable def sampled (bits : BitString) (m : Memory) : Memory :=
  Command.forwardCollected 46 42 47 Symbol.bit bits (counted m)

theorem counted_count (m : Memory) (graph : Graph) (start n : ℕ) (word : List Symbol)
    (result : Classify.Result m.store graph start n word) :
    ((counted m).store 46).length=width (graph.size+1)+2*graph.size := by
  simp [counted,Choose.sampleClock_eval,result.childSize,result.labelWidth]

theorem sampled_result (bits : BitString) (m : Memory) (graph : Graph) (start n : ℕ) (word : List Symbol)
    (result : Classify.Result m.store graph start n word) :
    Classify.Result (sampled bits m).store graph start n word := by
  apply result.of_frame
  intro i
  fin_cases i <;>
    simp [sampled,Command.forwardCollected,counted,Choose.sampleClock_eval,Classify.resultRegisters]

theorem sampled_bits (bits : BitString) (m : Memory) (graph : Graph) (start n : ℕ) (word : List Symbol)
    (result : Classify.Result m.store graph start n word) (random : m.randomHead=0) :
    (sampled bits m).store 42=(bits.take (width (graph.size+1)+2*graph.size)).map Symbol.bit := by
  change (((bits.drop (counted m).randomHead).take ((counted m).store 46).length).map Symbol.bit)=_
  rw [counted_count m graph start n word result]
  simp [counted,random]

theorem sampled_random (bits : BitString) (m : Memory) (graph : Graph) (start n : ℕ) (word : List Symbol)
    (result : Classify.Result m.store graph start n word) :
    (sampled bits m).randomHead=m.randomHead+(width (graph.size+1)+2*graph.size) := by
  change m.randomHead+((counted m).store 46).length=_
  rw [counted_count m graph start n word result]

def valueOutcome : Option (List Symbol) → Outcome Symbol
  | none => .exhausted
  | some word => .accepted word

noncomputable def chosen (bits : BitString) (m : Memory) : Memory :=
  {sampled bits m with store := Choose.routine.eval (sampled bits m).store}

noncomputable def randomBudget (bits : BitString) (m : Memory) : ℕ :=
  Choose.sampleClock.cost m.store+
    3*(m.store 42).length+3*(m.store 47).length+12*((counted m).store 46).length+
    Choose.routine.cost (sampled bits m).store+finishBudget (chosen bits m).store+bits.length+20

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
