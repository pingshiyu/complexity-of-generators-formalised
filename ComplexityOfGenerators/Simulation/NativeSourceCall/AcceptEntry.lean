import ComplexityOfGenerators.Simulation.NativeSourceCall.IndexStep

/-! A source acceptance reaches the actual cleanup entry without consuming
extra random bits or changing the emitted output. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem accept_entry (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (q : Fin M.states)
    (sourceTable : M.transition q none none (if head<length then some () else none) (source anchor) = .accept)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.source q) anchor c) :
    ∃ d, State M data fixed source visited (packet length head anchor) .clearEnd anchor d ∧
      (machine M).Steps data bits c (2*head+3) d ∧ WorkFrame (machine M) c d := by
  obtain ⟨fetched,fetchedState,fetchedPath,fetchedFrame⟩ := fetch M data bits fixed source visited length head within anchor q c represented
  have currentPacket : (read M (fetched.work fetched.workHead)).packet=some (mark length head head) := by
    rw [fetchedState.head, fetchedState.memory]
    exact packet_at_mark length head head anchor within
  have table : transition M (.fetch q (source anchor)) (fetched.work fetched.workHead) =
      .step (control M (.returning .accepted)) none .stay .stay .stay .stay none := by
    simp only [transition,currentPacket,mark,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
    rw [show (if decide (head=length) then (none : Option Unit) else some ()) =
      (if head<length then some () else none) by simpa only [mark] using index_symbol length head within,sourceTable]
  obtain ⟨start,startState,chosen,chosenFrame⟩ := fetchedState.silent bits (.returning .accepted) .stay table
  have startPosition : State M data fixed source visited (packet length head anchor) (.returning .accepted) (anchor+head) start := by
    simpa only [Move.onInt] using startState
  obtain ⟨d,doneState,returned,returnedFrame⟩ := returning M data bits fixed source visited length head within anchor .accepted start startPosition
  refine ⟨d,doneState,?_,(fetchedFrame.trans (machine M) chosenFrame).trans (machine M) returnedFrame⟩
  convert (fetchedPath.trans (machine M) chosen).trans (machine M) returned using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
