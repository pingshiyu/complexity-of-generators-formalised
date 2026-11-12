import ComplexityOfGenerators.Simulation.NativeSourceCall.LeftCarry

/-! One logical left move costs `2*j+3` native transitions, independently of
both the source work radius and its elapsed runtime. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem left_shift (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (q : Fin M.states)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.leftEnd q) anchor c) :
    ∃ d, State M data fixed source (insert (anchor-1) visited) (packet length head (anchor-1))
      (.source q) (anchor-1) d ∧
      (machine M).Steps data bits c (2*length+3) d ∧ WorkFrame (machine M) c d := by
  obtain ⟨last, lastState, forward, forwardFrame⟩ := represented.scan bits length .right (anchor+length)
    (fun t => anchor+t) (by simp) (by rfl)
    (by intro t before; simp [Move.onInt]; omega) (by
      intro t before input auxiliary index
      rw [machine_transition]
      have cellPacket : (read M (c.work (anchor+t))).packet=some (mark length head t) := by
        rw [represented.memory]
        exact packet_at_mark length head t anchor (by omega)
      have notLast : (mark length head t).last=false := by simp [mark, Nat.ne_of_lt before]
      simp [transition, cellPacket, notLast])
  have finalPacket : (read M (last.work last.workHead)).packet=some (mark length head length) := by
    rw [lastState.head, lastState.memory]
    exact packet_at_mark length head length anchor le_rfl
  obtain ⟨next, ready, first, firstFrame⟩ := lastState.packetStep bits (.leftCarry q (mark length head length))
    none .left (by simp [transition, finalPacket, mark])
  have initialBlock : State M data fixed source visited (leftBlock length head anchor 0)
      (.leftCarry q (mark length head (length-0))) (anchor+length-0-1) next := by
    simpa only [leftBlock_zero, Move.onInt, sub_zero, Nat.sub_zero] using ready
  obtain ⟨arrived, arrivedState, carried, carryFrame⟩ := left_carry M data bits fixed source visited
    length head anchor q 0 (Nat.zero_le _) next initialBlock
  obtain ⟨d, doneState, marked, markFrame⟩ := arrivedState.visitStep bits (.source q) (by rfl)
  refine ⟨d, doneState, ?_, ?_⟩
  · have combined := ((forward.trans (machine M) first).trans (machine M) carried).trans (machine M) marked
    convert combined using 1 <;> omega
  · exact ((forwardFrame.trans (machine M) firstFrame).trans (machine M) carryFrame).trans (machine M) markFrame

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
