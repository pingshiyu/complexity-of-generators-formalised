import ComplexityOfGenerators.Simulation.NativeSourceCall.State
import ComplexityOfGenerators.Simulation.NativeSourceCall.PacketUpdates

/-! Exact native execution of the rightward carry. Each old mark is read
before being overwritten, including the coincident endpoints at index zero. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

def mark (length head position : ℕ) : IndexMark :=
  ⟨decide (position=0), decide (position=length), decide (position=head)⟩

@[simp] theorem packet_at_mark (length head position : ℕ) (anchor : ℤ) (within : position≤length) :
    packet length head anchor (anchor+position)=some (mark length head position) :=
  packet_at length head position anchor within

theorem right_carry (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (q : Fin M.states) (count : ℕ) (within : count≤length)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (rightBlock length head anchor count)
      (.rightCarry q (mark length head count)) (anchor+count+1) c) :
    ∃ d, State M data fixed source visited (packet length head (anchor+1))
      (.rightReturn q) (anchor+length+1) d ∧
      (machine M).Steps data bits c (length-count+1) d ∧ WorkFrame (machine M) c d := by
  induction remainder : length-count generalizing count c with
  | zero =>
      have same : count=length := by omega
      subst count
      have table : transition M (.rightCarry q (mark length head length)) (c.work c.workHead) =
          .step (control M (.rightReturn q))
            (some (alphabet M {read M (c.work c.workHead) with packet := some (mark length head length)}))
            .stay .stay .stay .stay none := by simp [transition, mark]
      obtain ⟨d, ready, path, frame⟩ := represented.packetStep bits (.rightReturn q)
        (some (mark length head length)) .stay table
      have block : Function.update (rightBlock length head anchor length) (anchor+length+1)
          (some (mark length head length)) = packet length head (anchor+1) := by
        simpa only [packet_at_mark length head length anchor le_rfl] using rightBlock_finish length head anchor
      refine ⟨d, ?_, ?_, frame⟩
      · simpa only [block, Move.onInt] using ready
      · simpa only [Nat.sub_self, Nat.zero_add] using path
  | succ remaining ih =>
      have before : count<length := by omega
      have point : anchor+(count : ℤ)+1=anchor+(count+1 : ℕ) := by omega
      have cellPacket : (read M (c.work c.workHead)).packet = some (mark length head (count+1)) := by
        rw [represented.head, represented.memory, rightBlock_current, point]
        exact packet_at_mark length head (count+1) anchor (by omega)
      have notLast : (mark length head count).last=false := by simp [mark, Nat.ne_of_lt before]
      have table : transition M (.rightCarry q (mark length head count)) (c.work c.workHead) =
          .step (control M (.rightCarry q (mark length head (count+1))))
            (some (alphabet M {read M (c.work c.workHead) with packet := some (mark length head count)}))
            .right .stay .stay .stay none := by simp [transition, notLast, cellPacket]
      obtain ⟨next, nextState, edge, stepFrame⟩ := represented.packetStep bits
        (.rightCarry q (mark length head (count+1))) (some (mark length head count)) .right table
      have block : Function.update (rightBlock length head anchor count) (anchor+count+1)
          (some (mark length head count)) = rightBlock length head anchor (count+1) := by
        simpa only [packet_at_mark length head count anchor within] using rightBlock_step length head count anchor
      have shifted : State M data fixed source visited (rightBlock length head anchor (count+1))
          (.rightCarry q (mark length head (count+1))) (anchor+(count+1 : ℕ)+1) next := by
        have coordinate : Move.right.onInt (anchor+count+1)=anchor+(count+1 : ℕ)+1 := by simp [Move.onInt]; omega
        simpa only [block, coordinate] using nextState
      obtain ⟨d, ready, rest, restFrame⟩ := ih (count+1) (by omega) next shifted (by omega)
      refine ⟨d, ready, ?_, stepFrame.trans (machine M) restFrame⟩
      have cost : 1+(length-(count+1)+1)=length-count+1 := by omega
      convert edge.trans (machine M) rest using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
