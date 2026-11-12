import ComplexityOfGenerators.Simulation.NativeSourceCall.State
import ComplexityOfGenerators.Simulation.NativeSourceCall.RightCarry

/-! Fetching a source instruction and returning to the source head scan only
the virtual index block; their costs depend on its length, not work radius. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem fetch (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (q : Fin M.states)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.source q) anchor c) :
    ∃ d, State M data fixed source visited (packet length head anchor)
      (.fetch q (source anchor)) (anchor+head) d ∧
      (machine M).Steps data bits c (head+1) d ∧ WorkFrame (machine M) c d := by
  obtain ⟨first, firstState, initial, initialFrame⟩ := represented.silent bits (.fetch q (source anchor)) .stay (by
    simp only [transition, represented.head, represented.memory anchor])
  have firstPosition : State M data fixed source visited (packet length head anchor)
      (.fetch q (source anchor)) anchor first := by simpa only [Move.onInt] using firstState
  obtain ⟨d, ready, scanned, scanFrame⟩ := firstPosition.scan bits head .right (anchor+head)
    (fun t => anchor+t) (by simp) rfl
    (by intro t before; simp [Move.onInt]; omega) (by
      intro t before input auxiliary index
      rw [machine_transition]
      have currentPacket : (read M (first.work (anchor+t))).packet=some (mark length head t) := by
        rw [firstPosition.memory]
        exact packet_at_mark length head t anchor (by omega)
      have notHead : (mark length head t).head=false := by simp [mark, Nat.ne_of_lt before]
      simp [transition, currentPacket, notHead])
  refine ⟨d, ready, ?_, initialFrame.trans (machine M) scanFrame⟩
  convert initial.trans (machine M) scanned using 1 <;> omega

theorem returning_scan (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (action : Return O M.states M.symbols)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.returning action) (anchor+head) c) :
    ∃ d, State M data fixed source visited (packet length head anchor)
      (.returning action) anchor d ∧
      (machine M).Steps data bits c head d ∧ WorkFrame (machine M) c d := by
  apply represented.scan bits head .left anchor (fun t => anchor+head-t) (by omega) (by omega)
    (by intro t before; simp [Move.onInt]; omega)
  intro t before input auxiliary index
  rw [machine_transition]
  have notFirst : (read M (c.work (anchor+head-t))).packet.any IndexMark.first=false := by
    rw [represented.memory]
    have different : anchor+(head : ℤ)-t≠anchor := by omega
    exact Bool.eq_false_iff.mpr ((packet_first_iff length head anchor _).not.mpr different)
  simp only [transition, notFirst, Bool.false_eq_true, ↓reduceIte]

def afterReturn : Return O M.states M.symbols → Phase O M.states M.symbols
  | .resume q => .source q
  | .step action => .execute action
  | .accepted => .clearEnd

theorem returning (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (action : Return O M.states M.symbols)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.returning action) (anchor+head) c) :
    ∃ d, State M data fixed source visited (packet length head anchor)
      (afterReturn M action) anchor d ∧
      (machine M).Steps data bits c (head+1) d ∧ WorkFrame (machine M) c d := by
  obtain ⟨start, startState, scanned, scanFrame⟩ := returning_scan M data bits fixed source visited
    length head within anchor action c represented
  obtain ⟨d, ready, final, finalFrame⟩ := startState.silent bits (afterReturn M action) .stay (by
    cases action <;> simp only [afterReturn, transition, startState.head, startState.memory anchor, packet_first, ↓reduceIte])
  refine ⟨d, ?_, scanned.trans (machine M) final, scanFrame.trans (machine M) finalFrame⟩
  simpa only [Move.onInt] using ready

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
