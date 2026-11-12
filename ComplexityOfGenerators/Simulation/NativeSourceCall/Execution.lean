import ComplexityOfGenerators.Simulation.NativeSourceCall.AcceptReplay
import ComplexityOfGenerators.Simulation.NativeSourceCall.FailureReplay
import ComplexityOfGenerators.Simulation.NativeSourceCall.SourceBounds
import ComplexityOfGenerators.Simulation.NativeSourceCall.ReadHeads
import ComplexityOfGenerators.Simulation.NativeSourceCall.Cleanup
import ComplexityOfGenerators.Generators

/-! End-to-end prepared native source calls. Source work/output can be
unbounded; the overhead is linear in original source time and polynomial in the
selected unary index. No source variance or supported-output-length bound is
assumed. Actual caller preparation and control hooking remain separate. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem accepted_call (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length : ℕ) (target : Configuration (machine (F := F) M))
    (prepared : State M data fixed (fun _=>none) {0} (packet length 0 0) (.source M.initial) 0 target)
    (sourceTicks : ℕ) (finishSource : Configuration M)
    (path : M.Steps (generatorData length) (bits.drop target.randomHead) M.initialConfiguration sourceTicks finishSource)
    (word : List O) (accepted : M.observe (generatorData length) (bits.drop target.randomHead) finishSource=.halted (.accepted word)) :
    ∃ ticks finishTarget, ticks≤(4*length+16)*(sourceTicks+1) ∧
      State M data fixed (fun _=>none) ∅ (fun _=>none) .done 0 finishTarget ∧
      (machine M).Steps data bits target ticks finishTarget ∧
      finishTarget.randomHead=target.randomHead+finishSource.randomHead ∧
      finishTarget.output=target.output++word ∧
      finishTarget.inputHead=target.inputHead ∧ finishTarget.auxiliaryHead=target.auxiliaryHead ∧
      finishTarget.indexHead=target.indexHead := by
  have ready := ready_initial M data fixed length target prepared
  obtain ⟨replayTicks,entry,replayTime,entryState,replayPath,random,output⟩ := replay_accept M data bits fixed length
    target.randomHead target.output M.initialConfiguration finishSource target ready sourceTicks path word accepted
  have geometry := source_path_geometry M length _ sourceTicks finishSource path
  obtain ⟨cleanupTicks,finish,cleanupTime,finishState,cleanupPath,frame⟩ := cleanup M data bits fixed finishSource.work
    finishSource.visited length finishSource.indexHead finishSource.workHead entry geometry.interval geometry.head geometry.blank entryState
  have visitedBound := source_path_visited M length _ sourceTicks finishSource path
  have complete := replayPath.trans (machine M) cleanupPath
  have heads := steps_readHeads M data bits complete prepared.bounds
  refine ⟨replayTicks+cleanupTicks,finish,?_,finishState,complete,
    frame.random.trans random,frame.output.trans output,heads.2.1,heads.2.2.1,heads.2.2.2⟩
  calc
    replayTicks+cleanupTicks ≤ (4*length+12)*sourceTicks+2*length+3+(2*length+4*finishSource.visited.card+8) :=
      Nat.add_le_add replayTime cleanupTime
    _ ≤ (4*length+12)*sourceTicks+2*length+3+(2*length+4*(sourceTicks+1)+8) := by omega
    _ ≤ (4*length+16)*(sourceTicks+1) := by
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
      omega

/-- Every finite seed follows a terminating original-source path. The call does
not introduce explicit rejection when the original source never rejects. -/
theorem terminates_from_prepared (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length : ℕ) (target : Configuration (machine (F := F) M))
    (prepared : State M data fixed (fun _=>none) {0} (packet length 0 0) (.source M.initial) 0 target)
    (halting : M.HaltingTransducer (generatorData length)) :
    ∃ ticks result, (machine M).runFrom data bits target ticks=.halted result ∧ result≠.rejected := by
  obtain ⟨sourceTicks,result,run⟩ := halting.1 (bits.drop target.randomHead)
  obtain ⟨elapsed,within,finish,path,observation⟩ := M.runFrom_path (generatorData length)
    (bits.drop target.randomHead) M.initialConfiguration sourceTicks
  have terminal : M.observe (generatorData length) (bits.drop target.randomHead) finish=.halted result := by
    rw [← observation,M.runFrom_initial,run]
  cases result with
  | rejected => exact False.elim (halting.2 _ sourceTicks run)
  | exhausted =>
      have ready := ready_initial M data fixed length target prepared
      obtain ⟨ticks,time,exhausted⟩ := replay_exhausted M data bits fixed length target.randomHead target.output
        M.initialConfiguration finish target ready elapsed path terminal
      exact ⟨ticks,.exhausted,exhausted,by simp⟩
  | accepted word =>
      obtain ⟨ticks,finishTarget,time,state,replayed,random,output,heads⟩ := accepted_call M data bits fixed length target prepared elapsed finish path word terminal
      refine ⟨ticks,.accepted (target.output++word),?_,by simp⟩
      rw [replayed.runFrom (machine M)]
      simp only [Machine.observe,state.state,machine_transition,transition,output]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
