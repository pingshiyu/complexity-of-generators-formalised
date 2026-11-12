import ComplexityOfGenerators.Simulation.OriginalHeaderController.Native
import ComplexityOfGenerators.Simulation.OriginalHeaderController.WholeTrace
import ComplexityOfGenerators.Simulation.WordStack.EventNativeReturns
import ComplexityOfGenerators.Simulation.NativeEventTraceRebase

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack TransducerBank
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local semireducible] command
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound) (operation : Operation)

theorem machine_split_selected (n : ℕ) (header : List Bool) (requests : List Request) (bits : BitString)
    (choice : Choice operation n header requests) (preludeTicks : ℕ) (after : Memory (Cell selector) Event 35)
    (preludeRun : (prelude selector width clock).Runs n bits (initialMemory selector 0) preludeTicks (.done after))
    (state : FixedBlockRetry.State n (cap width clock n) after)
    (payload : after.store 31=header.map Symbol.letter) :
    ∃prefixTicks tailTicks tailStart last,
      (machine selector width clock operation).Steps (generatorData n) bits
        (machine selector width clock operation).initialConfiguration prefixTicks tailStart ∧
      tailStart.output=[] ∧ tailStart.randomHead=after.randomHead ∧
      (machine selector width clock operation).NativeEventTrace (parameter selector width clock operation)
        allowed (generatorData n) bits (eventList requests) tailStart last ∧
      (machine selector width clock operation).Steps (generatorData n) bits tailStart tailTicks last ∧
      last.randomHead=tailStart.randomHead ∧
      (machine selector width clock operation).observe (generatorData n) bits last=
        .halted (.accepted ((eventList requests).map Prod.fst)) := by
  letI := alphabetFintype selector
  letI := controlFintype selector width clock operation
  let A := (prelude selector width clock).program 0
  let T := (events selector operation).program 0
  let C := program selector width clock operation
  let f : (events selector operation).Control→(command selector width clock operation).Control := Sum.inr
  have tailEmbedding : T.Embeds C f := A.sequence_right T
  obtain ⟨q,purePath,pureTerminal⟩ := preludeRun.compiled 0 (by simp [initialMemory])
  have embedded := (A.sequence_left T).steps A purePath
  have transfer : C.Steps n bits (after.at (.inl q)) 1 (after.at (f T.initial)) := by
    apply WordStack.Program.Steps.go_at _ n bits after _ _ state.head
    change Instruction.redirect Sum.inl (.step (.inr T.initial) .stay .stay none) (A.instruction n (after.at q))=_
    rw [pureTerminal];rfl
  have prefixPath := embedded.trans C transfer
  obtain ⟨loaded,loadedReady,loadPath,_⟩ := bank_loaded_inRegion C.bank (generatorData n) bits 0
  have initialReady : BankReady C.bank (C.encoded ((initialMemory selector 0).at C.initial)) (fun _=>false) loaded := by
    change BankReady C.bank (C.encoded C.initialConfiguration) _ _
    rw [C.encoded_initial]
    exact loadedReady
  obtain ⟨prefixCost,tailStart,tailSides,tailReady,nativePrefix⟩ := C.steps_native prefixPath _
    (fun _=>false) loaded initialReady (C.encoded_bounded n _ (by simp [initialMemory,Memory.at,WordStack.Configuration.mapState]))
  have actualPrefix : (machine selector width clock operation).Steps (generatorData n) bits
      (machine selector width clock operation).initialConfiguration (1+prefixCost) tailStart := loadPath.trans _ nativePrefix
  have tailEmpty : tailStart.output=[] := tailReady.output.trans state.output
  have tailCursor : tailStart.randomHead=after.randomHead := tailReady.random
  obtain ⟨next,tailReturn,nextHead,nextRandom,nextOutput⟩ := events_eventReturns selector operation n bits header requests choice
    after state.head state.index payload
  obtain ⟨qt,wordTrace,wordTerminal⟩ := tailReturn
  have mapped := wordTrace.embeds tailEmbedding
  have finalTerminal : C.instruction n (next.at (f qt))=.accept := by
    change Instruction.redirect Sum.inr .accept (T.instruction n (next.at qt))=_
    rw [wordTerminal];rfl
  have correct := fun (e : Event) (j : ℕ) (store : Store selector) (heads : Fin 35→Option ℤ) memory
      (allowedJ : allowed e j) exported represented =>
    parameter_memory selector width clock operation e j store heads memory allowedJ exported represented
  obtain ⟨last,instrumented,accepted,lastCursor,_⟩ := mapped.native_terminal
    (parameter selector width clock operation) correct finalTerminal state.head tailSides tailStart tailReady
  obtain ⟨tailTicks,tailPath⟩ := instrumented.steps
  have terminal : (machine selector width clock operation).observe (generatorData n) bits last=
      .halted (.accepted ((eventList requests).map Prod.fst)) := by
    have outputEq : (WordStack.Configuration.mapState f (next.at qt)).output=(eventList requests).map Prod.fst := by
      change next.output=_
      rw [nextOutput,state.output,List.nil_append]
    rw [outputEq] at accepted
    exact accepted
  have stable : last.randomHead=tailStart.randomHead := by
    rw [lastCursor]
    change next.randomHead=tailStart.randomHead
    rw [nextRandom,tailReady.random]
    rfl
  exact ⟨1+prefixCost,tailTicks,tailStart,last,actualPrefix,tailEmpty,tailCursor,instrumented,tailPath,stable,terminal⟩

theorem machine_split_success (n failures : ℕ) (bits : BitString)
    (header : List Bool) (requests : List Request) (choice : Choice operation n header requests)
    (enough : (failures+1)*width n≤bits.length)
    (failed : ∀ k<failures,reference selector clock n ((bits.drop (k*width n)).take (width n))=none)
    (accepted : reference selector clock n ((bits.drop (failures*width n)).take (width n))=some header) :
    ∃prefixTicks tailTicks tailStart last,
      (machine selector width clock operation).Steps (generatorData n) bits
        (machine selector width clock operation).initialConfiguration prefixTicks tailStart ∧
      tailStart.output=[] ∧ tailStart.randomHead=(failures+1)*width n ∧
      (machine selector width clock operation).NativeEventTrace (parameter selector width clock operation)
        allowed (generatorData n) bits (eventList requests) tailStart last ∧
      (machine selector width clock operation).Steps (generatorData n) bits tailStart tailTicks last ∧
      last.randomHead=tailStart.randomHead ∧
      (machine selector width clock operation).observe (generatorData n) bits last=
        .halted (.accepted ((eventList requests).map Prod.fst)) ∧
      prefixTicks+tailTicks≤25*(primitiveCoefficient selector width clock n)^2*(failures+1)^2 := by
  obtain ⟨preludeTicks,_,after,preludeRun,state,cursor,payload⟩ := prelude_success selector width clock n 0 failures bits
    (by simpa using enough) (by simpa using failed) header (by simpa using accepted)
  obtain ⟨prefixTicks,tailTicks,tailStart,last,prefixPath,tailEmpty,tailCursor,trace,tailPath,stable,terminal⟩ :=
    machine_split_selected selector width clock operation n header requests bits choice preludeTicks after preludeRun state payload
  obtain ⟨nativeTicks,clockBound,clockRun⟩ := machine_runs_success selector width clock operation n failures bits header requests choice enough failed accepted
  obtain ⟨used,usedBound,oldLast,oldPath,oldObserved⟩ :=
    (machine selector width clock operation).runFrom_path (generatorData n) bits (machine selector width clock operation).initialConfiguration nativeTicks
  rw [(machine selector width clock operation).runFrom_initial] at oldObserved
  have oldTerminal := oldObserved.symm.trans clockRun
  have lengthBound := ((prefixPath.trans _ tailPath).le_terminal _ oldPath oldTerminal).trans usedBound
  refine ⟨prefixTicks,tailTicks,tailStart,last,prefixPath,tailEmpty,?_,trace,tailPath,stable,terminal,lengthBound.trans clockBound⟩
  simpa only [Nat.zero_add] using tailCursor.trans cursor

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
