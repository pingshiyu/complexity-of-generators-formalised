import ComplexityOfGenerators.Simulation.OriginalHeaderController.NativeSplit
import ComplexityOfGenerators.Simulation.WordStack.ExhaustedCompilation

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local semireducible] command
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound) (operation : Operation)

/-- Finite exhaustion occurs before any call event; a selected header instead
enters a deterministic tail carrying its concrete full-block certificate. -/
theorem machine_split_total (n : ℕ) (bits : BitString)
    (shape : Shape selector width clock operation n) :
    (∃ ticks last,
      (machine selector width clock operation).Steps (generatorData n) bits
        (machine selector width clock operation).initialConfiguration ticks last ∧
      last.output=[] ∧ (machine selector width clock operation).observe (generatorData n) bits last=.halted .exhausted) ∨
    ∃ header : List Bool, ∃ requests : List Request, Choice operation n header requests ∧
      (∃block,block.length=width n ∧ reference selector clock n block=some header) ∧
      ∃ prefixTicks tailTicks tailStart last,
        (machine selector width clock operation).Steps (generatorData n) bits
          (machine selector width clock operation).initialConfiguration prefixTicks tailStart ∧
        tailStart.output=[] ∧
        (machine selector width clock operation).NativeEventTrace (parameter selector width clock operation)
          allowed (generatorData n) bits (eventList requests) tailStart last ∧
        (machine selector width clock operation).Steps (generatorData n) bits tailStart tailTicks last ∧
        last.randomHead=tailStart.randomHead ∧
        (machine selector width clock operation).observe (generatorData n) bits last=
          .halted (.accepted ((eventList requests).map Prod.fst)) := by
  letI := alphabetFintype selector
  letI := controlFintype selector width clock operation
  obtain ⟨preludeTicks,result,preludeRun,post⟩ := prelude_total selector width clock n 0 bits
  cases result with
  | exhausted =>
      have execution := preludeRun.compiled 0 (by simp [initialMemory])
      let A := (prelude selector width clock).program 0
      let T := (events selector operation).program 0
      let C := program selector width clock operation
      have embedded : A.Embeds C Sum.inl := A.sequence_left T
      exact Or.inl (WordStack.Program.Executes.exhausted_native_of_embeds A C execution
        (prelude_noEmit selector width clock) Sum.inl embedded rfl)
  | done after =>
      obtain ⟨state,canonical,selected⟩ := post
      obtain ⟨header,requests,payload,choice,hit⟩ :=
        prelude_shape selector width clock operation n 0 bits shape after canonical selected
      obtain ⟨prefixTicks,tailTicks,tailStart,last,head,headEmpty,_,trace,tail,stable,terminal⟩ :=
        machine_split_selected selector width clock operation n header requests bits choice
          preludeTicks after preludeRun state payload
      exact Or.inr ⟨header,requests,choice,hit,prefixTicks,tailTicks,tailStart,last,head,headEmpty,
        trace,tail,stable,terminal⟩

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
