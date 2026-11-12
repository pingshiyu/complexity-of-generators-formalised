import ComplexityOfGenerators.Simulation.NativeSourceCall.RightCarry

/-! One logical right move translates only the bounded index packet. Its exact
native cost is `2*j+4`, independently of the source work-head coordinate. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem right_shift (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (q : Fin M.states)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.rightBegin q) anchor c) :
    ∃ d, State M data fixed source (insert (anchor+1) visited) (packet length head (anchor+1))
      (.source q) (anchor+1) d ∧
      (machine M).Steps data bits c (2*length+4) d ∧ WorkFrame (machine M) c d := by
  have initialPacket : (read M (c.work c.workHead)).packet = some (mark length head 0) := by
    rw [represented.head, represented.memory]
    simpa using packet_at_mark length head 0 anchor (Nat.zero_le _)
  obtain ⟨next, ready, first, firstFrame⟩ := represented.packetStep bits (.rightCarry q (mark length head 0))
    none .right (by simp [transition, initialPacket])
  have initialBlock : State M data fixed source visited (rightBlock length head anchor 0)
      (.rightCarry q (mark length head 0)) (anchor+0+1) next := by
    simpa only [rightBlock_zero, Move.onInt, add_zero] using ready
  obtain ⟨last, lastState, carried, carryFrame⟩ := right_carry M data bits fixed source visited
    length head anchor q 0 (Nat.zero_le _) next initialBlock
  obtain ⟨start, startState, back, backFrame⟩ := lastState.scan bits length .left (anchor+1)
    (fun t => anchor+length+1-t) (by omega) (by omega)
    (by intro t before; simp [Move.onInt]; omega) (by
      intro t before input auxiliary index
      rw [machine_transition]
      have notFirst : (read M (last.work (anchor+length+1-t))).packet.any IndexMark.first = false := by
        rw [lastState.memory]
        have different : anchor+(length : ℤ)+1-t ≠ anchor+1 := by omega
        exact Bool.eq_false_iff.mpr ((packet_first_iff length head (anchor+1) _).not.mpr different)
      simp only [transition, notFirst, Bool.false_eq_true, ↓reduceIte])
  obtain ⟨arrived, arrivedState, endScan, endFrame⟩ := startState.silent bits (.arrive q) .stay (by
    simp only [transition, startState.head, startState.memory (anchor+1), packet_first, ↓reduceIte])
  have arrivedPosition : State M data fixed source visited (packet length head (anchor+1))
      (.arrive q) (anchor+1) arrived := by simpa only [Move.onInt] using arrivedState
  obtain ⟨d, doneState, marked, markFrame⟩ := arrivedPosition.visitStep bits (.source q) (by rfl)
  refine ⟨d, doneState, ?_, ?_⟩
  · have combined := (((first.trans (machine M) carried).trans (machine M) back).trans (machine M) endScan).trans (machine M) marked
    convert combined using 1 <;> omega
  · exact (((firstFrame.trans (machine M) carryFrame).trans (machine M) backFrame).trans
      (machine M) endFrame).trans (machine M) markFrame

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
