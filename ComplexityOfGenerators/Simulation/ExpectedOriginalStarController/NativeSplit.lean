import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Export
import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.WholeTrace
import ComplexityOfGenerators.Simulation.WordStack.EventNativeReturns
import ComplexityOfGenerators.Simulation.NativeEventTraceRebase

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

theorem machine_split_selected (n : ℕ) (parts : List ℕ) (bits : BitString)
    (pathTicks : ℕ) (after : Memory (Cell M) Unit 80)
    (pathRun : (pathRetry M p).Runs n bits (readyMemory M n 0) pathTicks (.done after))
    (origin : after.indexHead=0) (empty : after.output=[])
    (path : after.store 31=pathWord M parts)
    (sizes : StoreBound after.store (CertifiedStarPhase.cap p n))
    (positive : ∀ j∈parts,0<j) :
    ∃ prefixTicks tailTicks tailStart last,
      (machine M p).Steps (generatorData n) bits (machine M p).initialConfiguration prefixTicks tailStart ∧
      tailStart.output=[] ∧ tailStart.randomHead=after.randomHead ∧
      (machine M p).NativeEventTrace (parameter M p) allowed (generatorData n) bits
        (parts.map (fun j=>((),j))) tailStart last ∧
      (machine M p).Steps (generatorData n) bits tailStart tailTicks last ∧
      last.randomHead=tailStart.randomHead ∧
      (machine M p).observe (generatorData n) bits last=.halted (.accepted (List.replicate parts.length ())) := by
  letI := alphabetFintype M
  letI := controlFintype M p
  let A := (prelude M p).program 0
  let T := (events M).program 0
  let C := program M p
  let f : (events M).Control→(command M p).Control := Sum.inr
  have tailEmbedding : T.Embeds C f := A.sequence_right T
  obtain ⟨_,_,bootRun⟩ := boot_runs M n 0 bits
  have prefixRun := prelude_of_runs M p bootRun pathRun empty
  obtain ⟨q,purePath,pureTerminal⟩ := prefixRun.compiled 0 (by simp [initialMemory])
  have embedded := (A.sequence_left T).steps A purePath
  have transfer : C.Steps n bits (after.at (.inl q)) 1 (after.at (f T.initial)) := by
    apply WordStack.Program.Steps.go_at _ n bits after _ _ (by omega)
    change Instruction.redirect Sum.inl (.step (.inr T.initial) .stay .stay none)
      (A.instruction n (after.at q)) = _
    rw [pureTerminal]; rfl
  have prefixPath := embedded.trans C transfer
  obtain ⟨loaded,loadedReady,loadPath,_⟩ := bank_loaded_inRegion C.bank (generatorData n) bits 0
  have initialReady : BankReady C.bank (C.encoded ((initialMemory M 0).at C.initial)) (fun _=>false) loaded := by
    change BankReady C.bank (C.encoded C.initialConfiguration) _ _
    rw [C.encoded_initial]
    exact loadedReady
  obtain ⟨prefixCost,tailStart,tailSides,tailReady,nativePrefix⟩ := C.steps_native prefixPath _
    (fun _=>false) loaded initialReady (C.encoded_bounded n _ (by simp [initialMemory,Memory.at,WordStack.Configuration.mapState]))
  have actualPrefix : (machine M p).Steps (generatorData n) bits (machine M p).initialConfiguration
      (1+prefixCost) tailStart := loadPath.trans _ nativePrefix
  have tailEmpty : tailStart.output=[] := tailReady.output.trans empty
  have tailCursor : tailStart.randomHead=after.randomHead := tailReady.random
  obtain ⟨next,tailReturn,nextRandom,nextOutput⟩ := events_eventReturns M n bits parts after
    (CertifiedStarPhase.cap p n) origin path sizes positive
  obtain ⟨qt,wordTrace,wordTerminal⟩ := tailReturn
  have mapped := wordTrace.embeds tailEmbedding
  have finalTerminal : C.instruction n (next.at (f qt))=.accept := by
    change Instruction.redirect Sum.inr .accept (T.instruction n (next.at qt)) = _
    rw [wordTerminal]; rfl
  have correct := fun (e : Unit) (j : ℕ) (store : Store M) (heads : Fin 80→Option ℤ) memory
      (allowedJ : allowed e j) exported represented =>
    parameter_memory M p store heads memory j allowedJ exported represented
  obtain ⟨last,instrumented,accepted,lastCursor,_⟩ :=
    mapped.native_terminal (parameter M p) correct finalTerminal (by change after.indexHead≤n; omega) tailSides tailStart tailReady
  obtain ⟨tailTicks,tailPath⟩ := instrumented.steps
  have terminal : (machine M p).observe (generatorData n) bits last=
      .halted (.accepted (List.replicate parts.length ())) := by
    have outputEq : (WordStack.Configuration.mapState f (next.at qt)).output=List.replicate parts.length () := by
      change next.output=_
      rw [nextOutput,empty,List.nil_append]
    rw [outputEq] at accepted
    exact accepted
  have cursorStable : last.randomHead=tailStart.randomHead := by
    rw [lastCursor]
    change next.randomHead=tailStart.randomHead
    rw [nextRandom,tailReady.random]
    rfl
  exact ⟨1+prefixCost,tailTicks,tailStart,last,actualPrefix,tailEmpty,tailCursor,instrumented,tailPath,
    cursorStable,terminal⟩

theorem machine_split_success (n failures : ℕ) (parts : List ℕ) (bits : BitString)
    (total : parts.sum=n) (positive : ∀ j∈parts,0<j)
    (enough : (failures+1)*StarCertification.width p n≤bits.length)
    (failed : ∀ k<failures, CertifiedStarPhase.value M p n
      ((bits.drop (k*StarCertification.width p n)).take (StarCertification.width p n))=none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (failures*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts)) :
    ∃ prefixTicks tailTicks tailStart last,
      (machine M p).Steps (generatorData n) bits (machine M p).initialConfiguration prefixTicks tailStart ∧
      tailStart.output=[] ∧ tailStart.randomHead=(failures+1)*StarCertification.width p n ∧
      (machine M p).NativeEventTrace (parameter M p) allowed (generatorData n) bits
        (parts.map (fun j=>((),j))) tailStart last ∧
      (machine M p).Steps (generatorData n) bits tailStart tailTicks last ∧
      last.randomHead=tailStart.randomHead ∧
      (machine M p).observe (generatorData n) bits last=.halted (.accepted (List.replicate parts.length ())) ∧
      prefixTicks+tailTicks≤25*(primitiveCoefficient M p n)^2*(failures+1)^2 := by
  obtain ⟨pathTicks,_,after,pathRun,origin,randomHead,empty,path,sizes⟩ :=
    pathRetry_runs_success M p n 0 failures parts bits
      (by simpa using enough) (by simpa using failed) (by simpa using success)
  obtain ⟨prefixTicks,tailTicks,tailStart,last,prefixPath,tailEmpty,tailCursor,trace,tailPath,stable,terminal⟩ :=
    machine_split_selected M p n parts bits pathTicks after pathRun origin empty path sizes positive
  obtain ⟨clock,clockBound,clockRun⟩ := machine_runs_success M p n failures parts bits total positive enough failed success
  obtain ⟨used,usedBound,oldLast,oldPath,oldObserved⟩ :=
    (machine M p).runFrom_path (generatorData n) bits (machine M p).initialConfiguration clock
  rw [(machine M p).runFrom_initial] at oldObserved
  have oldTerminal := oldObserved.symm.trans clockRun
  have lengthBound := ((prefixPath.trans _ tailPath).le_terminal (machine M p) oldPath oldTerminal).trans usedBound
  refine ⟨prefixTicks,tailTicks,tailStart,last,prefixPath,tailEmpty,?_,trace,tailPath,stable,terminal,
    lengthBound.trans clockBound⟩
  simpa only [Nat.zero_add] using tailCursor.trans randomHead

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
