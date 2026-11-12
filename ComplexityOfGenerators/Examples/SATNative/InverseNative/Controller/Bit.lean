import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Representation
import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Output

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] InverseNative.bodyTransform transform

def maskBudget (n : ℕ) (s : Store) : ℕ :=
  3*(s 31).length+3*(s 33).length+3*(s 30).length+26*n+8

def finishBitBudget (bit : Bool) (n : ℕ) (bits : BitString) (m : Memory) : ℕ :=
  let ready := (masked n bits m).store
  let output := (transform bit).eval ready
  maskBudget n m.store+(transform bit).cost ready+3*(output 28).length+10*(output 21).length+8

theorem finishBit_full (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (counter : m.store 32 = List.replicate n .zero)
    (represented : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ m.store)
    (clock : NativeBody.tokenCount formula ≤ (m.store 16).length)
    (available : m.randomHead+n ≤ bits.length) :
    ∃ ticks ≤ finishBitBudget bit n bits m, ∃ final,
      (finishBit bit).Runs n bits m ticks (.done final) ∧
        final.output = m.output ++
          (formula.lift active bit (choiceRows formula ((bits.drop m.randomHead).take n))).encode capacity (active+1) := by
  obtain ⟨maskTicks,maskCost,maskRun⟩ := prepareMask_full n bits m index counter available
  let ready := masked n bits m
  have readyRep := masked_represents capacity active _ m n bits represented
  have clockEq : ready.store 16 = m.store 16 := (masked_fields n bits m).2 16 (by decide) (by decide) (by decide)
  have readyClock : NativeBody.tokenCount formula ≤ (ready.store 16).length := by rw [clockEq]; exact clock
  have readyMask := (masked_fields n bits m).1
  have buffer := transform_buffer bit bound formula valid ready.store readyRep readyClock
    ((bits.drop m.randomHead).take n) readyMask
  obtain ⟨bodyTicks,bodyCost,bodyRun⟩ := (transform bit).runs bits ready index
  let output : Memory := {ready with store := (transform bit).eval ready.store}
  obtain ⟨emitTicks,emitCost,final,emits,emitted⟩ := emitBuffer_runs bits output index
  have result : final.output = m.output ++
      (formula.lift active bit (choiceRows formula ((bits.drop m.randomHead).take n))).encode capacity (active+1) := by
    change final.output = ready.output ++ ((transform bit).eval ready.store 21).reverse at emitted
    rw [buffer,List.reverse_reverse] at emitted
    exact emitted
  have run := Command.Runs.seq _ _ _ _ _ _ _ maskRun (Command.Runs.seq _ _ _ _ _ _ _ bodyRun emits)
  refine ⟨maskTicks+1+(bodyTicks+1+emitTicks),?_,final,run,result⟩
  dsimp only [finishBitBudget,maskBudget]
  change bodyTicks ≤ (transform bit).cost ready.store at bodyCost
  change emitTicks ≤ 3*(output.store 28).length+10*(output.store 21).length+2 at emitCost
  dsimp only [output,ready] at emitCost bodyCost
  omega

theorem finishBit_short (bit : Bool) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (counter : m.store 32 = List.replicate n .zero)
    (random : m.randomHead ≤ bits.length) (short : bits.length < m.randomHead+n) :
    ∃ ticks ≤ finishBitBudget bit n bits m, (finishBit bit).Runs n bits m ticks .exhausted := by
  obtain ⟨ticks,cost,run⟩ := prepareMask_short n bits m index counter random short
  refine ⟨ticks,?_,Command.Runs.seq_absent _ _ _ ticks run⟩
  dsimp only [finishBitBudget,maskBudget]
  omega

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
