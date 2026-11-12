import ComplexityOfGenerators.Simulation.NativeSourceCall.RightCarry

/-! The leftward carry is the symmetric overwrite-safe packet translation. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem left_carry (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (q : Fin M.states) (count : ℕ) (within : count≤length)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (leftBlock length head anchor count)
      (.leftCarry q (mark length head (length-count))) (anchor+length-count-1) c) :
    ∃ d, State M data fixed source visited (packet length head (anchor-1))
      (.arrive q) (anchor-1) d ∧
      (machine M).Steps data bits c (length-count+1) d ∧ WorkFrame (machine M) c d := by
  induction remainder : length-count generalizing count c with
  | zero =>
      have same : count=length := by omega
      subst count
      have table : transition M (.leftCarry q (mark length head (length-length))) (c.work c.workHead) =
          .step (control M (.arrive q))
            (some (alphabet M {read M (c.work c.workHead) with packet := some (mark length head 0)}))
            .stay .stay .stay .stay none := by simp [transition, mark]
      obtain ⟨d, ready, path, frame⟩ := represented.packetStep bits (.arrive q)
        (some (mark length head 0)) .stay table
      have point : anchor+(length : ℤ)-length-1=anchor-1 := by omega
      have block : Function.update (leftBlock length head anchor length) (anchor-1)
          (some (mark length head 0)) = packet length head (anchor-1) := by
        simpa only [show packet length head anchor anchor=some (mark length head 0) by
          simpa using packet_at_mark length head 0 anchor (Nat.zero_le _)] using leftBlock_finish length head anchor
      refine ⟨d, ?_, ?_, frame⟩
      · simpa only [Move.onInt, point, block] using ready
      · simpa only [Nat.sub_self, Nat.zero_add] using path
  | succ remaining ih =>
      have before : count<length := by omega
      have point : anchor+(length : ℤ)-count-1=anchor+(length-(count+1) : ℕ) := by omega
      have cellPacket : (read M (c.work c.workHead)).packet = some (mark length head (length-(count+1))) := by
        rw [represented.head, represented.memory, leftBlock_current, point]
        exact packet_at_mark length head (length-(count+1)) anchor (by omega)
      have notFirst : (mark length head (length-count)).first=false := by simp [mark, show length-count≠0 by omega]
      have table : transition M (.leftCarry q (mark length head (length-count))) (c.work c.workHead) =
          .step (control M (.leftCarry q (mark length head (length-(count+1)))))
            (some (alphabet M {read M (c.work c.workHead) with packet := some (mark length head (length-count))}))
            .left .stay .stay .stay none := by simp [transition, notFirst, cellPacket]
      obtain ⟨next, nextState, edge, stepFrame⟩ := represented.packetStep bits
        (.leftCarry q (mark length head (length-(count+1)))) (some (mark length head (length-count))) .left table
      have carryPoint : anchor+(length : ℤ)-count=anchor+(length-count : ℕ) := by omega
      have block : Function.update (leftBlock length head anchor count) (anchor+length-count-1)
          (some (mark length head (length-count))) = leftBlock length head anchor (count+1) := by
        simpa only [carryPoint, packet_at_mark length head (length-count) anchor (Nat.sub_le _ _)] using
          leftBlock_step length head count anchor
      have shifted : State M data fixed source visited (leftBlock length head anchor (count+1))
          (.leftCarry q (mark length head (length-(count+1)))) (anchor+length-(count+1 : ℕ)-1) next := by
        have coordinate : Move.left.onInt (anchor+length-count-1)=anchor+length-(count+1 : ℕ)-1 := by simp [Move.onInt]; omega
        simpa only [block, coordinate] using nextState
      obtain ⟨d, ready, rest, restFrame⟩ := ih (count+1) (by omega) next shifted (by omega)
      refine ⟨d, ready, ?_, stepFrame.trans (machine M) restFrame⟩
      have cost : 1+(length-(count+1)+1)=length-count+1 := by omega
      convert edge.trans (machine M) rest using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
