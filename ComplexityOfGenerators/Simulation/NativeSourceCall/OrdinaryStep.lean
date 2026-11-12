import ComplexityOfGenerators.Simulation.NativeSourceCall.IndexStep
import ComplexityOfGenerators.Simulation.NativeSourceCall.SourceWrite
import ComplexityOfGenerators.Simulation.NativeSourceCall.LeftShift
import ComplexityOfGenerators.Simulation.NativeSourceCall.RightShift
import ComplexityOfGenerators.Simulation.NativeSourceCall.Frame

/-! One ordinary source instruction has native overhead linear in its index.
No bound is imposed on the source work tape or the number of symbols emitted
by the whole call. The physical output prefix is preserved exactly. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem ordinary_step (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (visitedHead : anchor∈visited)
    (q next : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (sourceTable : M.transition q none none (if head<length then some () else none) (source anchor) =
      .step next write work input auxiliary index emit)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.source q) anchor c) :
    ∃ ticks d, ticks≤4*length+12 ∧
      State M data fixed (Function.update source anchor (write.or (source anchor)))
        (insert (work.onInt anchor) visited) (packet length (index.onInput length head) (work.onInt anchor))
        (.source next) (work.onInt anchor) d ∧
      (machine M).Steps data bits c ticks d ∧ Frame M emit.toList c d := by
  obtain ⟨fetched,fetchedState,fetchedPath,fetchedFrame⟩ := fetch M data bits fixed source visited
    length head within anchor q c represented
  obtain ⟨indexed,indexedState,indexedPath,indexedFrame⟩ := index_step M data bits fixed source visited
    length head within anchor q next (source anchor) write work input auxiliary index emit sourceTable fetched fetchedState
  have nextWithin := index.onInput_le length head within
  obtain ⟨returned,returnedState,returnedPath,returnedFrame⟩ := returning M data bits fixed source visited
    length (index.onInput length head) nextWithin anchor (.step ⟨next,write,work,emit⟩) indexed indexedState
  have executionState : State M data fixed source visited (packet length (index.onInput length head) anchor)
      (.execute ⟨next,write,work,emit⟩) anchor returned := returnedState
  obtain ⟨written,writtenState,writtenPath,random,inputHead,auxiliaryHead,indexHead,output⟩ :=
    source_write M data bits fixed source visited (packet length (index.onInput length head) anchor)
      anchor ⟨next,write,work,emit⟩ returned executionState
  have writeFrame : Frame M emit.toList returned written := ⟨random,inputHead,auxiliaryHead,indexHead,output⟩
  obtain ⟨shiftTicks,d,shiftBound,doneState,shifted,shiftFrame⟩ :
      ∃ ticks d, ticks≤2*length+4 ∧
        State M data fixed (Function.update source anchor (write.or (source anchor)))
          (insert (work.onInt anchor) visited) (packet length (index.onInput length head) (work.onInt anchor))
          (.source next) (work.onInt anchor) d ∧
        (machine M).Steps data bits written ticks d ∧ WorkFrame (machine M) written d := by
    cases work with
    | stay =>
        refine ⟨0,written,by omega,?_,.refl,WorkFrame.refl (machine M) written⟩
        simpa only [afterExecute,Move.onInt,Finset.insert_eq_of_mem visitedHead] using writtenState
    | left =>
        obtain ⟨d,doneState,path,frame⟩ := left_shift M data bits fixed
          (Function.update source anchor (write.or (source anchor))) visited length (index.onInput length head)
          anchor next written writtenState
        exact ⟨2*length+3,d,by omega,doneState,path,frame⟩
    | right =>
        obtain ⟨d,doneState,path,frame⟩ := right_shift M data bits fixed
          (Function.update source anchor (write.or (source anchor))) visited length (index.onInput length head)
          anchor next written writtenState
        exact ⟨2*length+4,d,le_rfl,doneState,path,frame⟩
  refine ⟨(head+1)+2+(index.onInput length head+1)+1+shiftTicks,d,by omega,doneState,?_,?_⟩
  · exact (((fetchedPath.trans (machine M) indexedPath).trans (machine M) returnedPath).trans
      (machine M) writtenPath).trans (machine M) shifted
  · exact (Frame.beforeWork ((fetchedFrame.trans (machine M) indexedFrame).trans
      (machine M) returnedFrame) writeFrame).afterWork shiftFrame

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
