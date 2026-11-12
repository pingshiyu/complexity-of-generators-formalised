import ComplexityOfGenerators.Simulation.NativeSourceCall.IndexStep

/-! A source random instruction consumes exactly one real source bit. Index
fetch/return instructions do not consume randomness or emit output. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem random_step (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (q no yes : Fin M.states)
    (sourceTable : M.transition q none none (if head<length then some () else none) (source anchor) = .readRandom no yes)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.source q) anchor c)
    (bit : Bool) (lookup : bits[c.randomHead]?=some bit) :
    ∃ d, State M data fixed source visited (packet length head anchor) (.source (if bit then yes else no)) anchor d ∧
      (machine M).Steps data bits c (2*head+3) d ∧ d.randomHead=c.randomHead+1 ∧
      d.inputHead=c.inputHead ∧ d.auxiliaryHead=c.auxiliaryHead ∧ d.indexHead=c.indexHead ∧ d.output=c.output := by
  obtain ⟨fetched,fetchedState,fetchedPath,fetchedFrame⟩ := fetch M data bits fixed source visited length head within anchor q c represented
  have currentPacket : (read M (fetched.work fetched.workHead)).packet=some (mark length head head) := by
    rw [fetchedState.head, fetchedState.memory]
    exact packet_at_mark length head head anchor within
  have table : transition M (.fetch q (source anchor)) (fetched.work fetched.workHead) =
      .readRandom (control M (.returning (.resume no))) (control M (.returning (.resume yes))) := by
    simp only [transition,currentPacket,mark,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
    rw [show (if decide (head=length) then (none : Option Unit) else some ()) =
      (if head<length then some () else none) by simpa only [mark] using index_symbol length head within,sourceTable]
  let chosen : Configuration (machine (F := F) M) :=
    {fetched with
      state := control M (.returning (.resume (if bit then yes else no)))
      randomHead := fetched.randomHead+1}
  have chosenState : State M data fixed source visited (packet length head anchor)
      (.returning (.resume (if bit then yes else no))) (anchor+head) chosen :=
    ⟨fetchedState.memory,rfl,fetchedState.head,
      ⟨fetchedState.bounds.input,fetchedState.bounds.auxiliary,fetchedState.bounds.index⟩⟩
  have randomPath : (machine M).Steps data bits fetched 1 chosen := by
    apply Machine.Steps.tail .refl
    have actualTable : (machine M).transition fetched.state data.input[fetched.inputHead]?
        data.auxiliary[fetched.auxiliaryHead]? (if fetched.indexHead<data.index then some () else none)
        (fetched.work fetched.workHead)=
        .readRandom (control M (.returning (.resume no))) (control M (.returning (.resume yes))) := by
      rw [fetchedState.state,machine_transition]
      exact table
    simp only [Machine.next,actualTable,fetchedFrame.random,lookup]
    cases bit <;> simp [chosen,fetchedFrame.random]
  obtain ⟨d,doneState,returned,returnedFrame⟩ := returning M data bits fixed source visited length head within anchor
    (.resume (if bit then yes else no)) chosen chosenState
  refine ⟨d,doneState,?_,?_,?_,?_,?_,?_⟩
  · convert (fetchedPath.trans (machine M) randomPath).trans (machine M) returned using 1 <;> omega
  · exact returnedFrame.random.trans (congrArg (·+1) fetchedFrame.random)
  · exact returnedFrame.input.trans fetchedFrame.input
  · exact returnedFrame.auxiliary.trans fetchedFrame.auxiliary
  · exact returnedFrame.index.trans fetchedFrame.index
  · exact returnedFrame.output.trans fetchedFrame.output

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
