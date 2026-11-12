import ComplexityOfGenerators.Simulation.NativeSourceCall.Fetch
import ComplexityOfGenerators.Simulation.NativeSourceCall.IndexUpdates

/-! Updating the virtual read-only index uses exactly two native writes. The
source work/output part of the instruction is retained in finite control. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem index_symbol (length head : ℕ) (within : head≤length) :
    (if (mark length head head).last then (none : Option Unit) else some ()) =
      if head<length then some () else none := by
  by_cases last : head=length
  · simp [mark, last]
  · have before : head<length := by omega
    simp [mark, last, before]

theorem index_step (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ)
    (q next : Fin M.states) (cached write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (sourceTable : M.transition q none none (if head<length then some () else none) cached =
      .step next write work input auxiliary index emit)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor)
      (.fetch q cached) (anchor+head) c) :
    ∃ d, State M data fixed source visited (packet length (index.onInput length head) anchor)
      (.returning (.step ⟨next,write,work,emit⟩)) (anchor+(index.onInput length head : ℕ)) d ∧
      (machine M).Steps data bits c 2 d ∧ WorkFrame (machine M) c d := by
  have currentPacket : (read M (c.work c.workHead)).packet=some (mark length head head) := by
    rw [represented.head, represented.memory]
    exact packet_at_mark length head head anchor within
  have table : transition M (.fetch q cached) (c.work c.workHead) =
      .step (control M (.placeIndex ⟨next,write,work,emit⟩))
        (some (alphabet M {read M (c.work c.workHead) with
          packet := some {mark length head head with head := false}}))
        (indexMove (mark length head head) index) .stay .stay .stay none := by
    simp only [transition, currentPacket, mark, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show (if decide (head=length) then (none : Option Unit) else some ()) =
      (if head<length then some () else none) by simpa only [mark] using index_symbol length head within,
      sourceTable]
  obtain ⟨middle, middleState, first, firstFrame⟩ := represented.packetStep bits
    (.placeIndex ⟨next,write,work,emit⟩) (some {mark length head head with head := false})
    (indexMove (mark length head head) index) table
  have cleared : State M data fixed source visited (headless length anchor)
      (.placeIndex ⟨next,write,work,emit⟩) (anchor+(index.onInput length head : ℕ)) middle := by
    have coordinate := indexMove_correct length head within anchor index
    simpa only [mark, decide_true, clear_head length head within anchor, coordinate] using middleState
  have nextWithin := index.onInput_le length head within
  have nextPacket : (read M (middle.work middle.workHead)).packet =
      some ⟨decide (index.onInput length head=0),decide (index.onInput length head=length),false⟩ := by
    rw [cleared.head, cleared.memory]
    exact headless_at length _ nextWithin anchor
  obtain ⟨d, finalState, final, finalFrame⟩ := cleared.packetStep bits
    (.returning (.step ⟨next,write,work,emit⟩))
    (some ⟨decide (index.onInput length head=0),decide (index.onInput length head=length),true⟩)
    .stay (by simp only [transition, nextPacket])
  refine ⟨d, ?_, first.trans (machine M) final, firstFrame.trans (machine M) finalFrame⟩
  simpa only [place_head length _ nextWithin anchor, Move.onInt] using finalState

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
