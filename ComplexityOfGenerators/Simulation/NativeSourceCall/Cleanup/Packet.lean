import ComplexityOfGenerators.Simulation.NativeSourceCall.State

/-! Erasing the moving unary index costs twice its length plus two steps. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

def remainingPacket (length head remaining : ℕ) (anchor position : ℤ) : Option IndexMark :=
  if position ≤ anchor+remaining then packet length head anchor position else none

theorem remainingPacket_full (length head : ℕ) (anchor : ℤ) :
    remainingPacket length head length anchor = packet length head anchor := by
  funext x
  unfold remainingPacket packet
  split_ifs <;> simp_all <;> omega

theorem remainingPacket_at (length head remaining : ℕ) (within : remaining≤length) (anchor : ℤ) :
    remainingPacket length head remaining anchor (anchor+remaining) =
      some ⟨decide (remaining=0),decide (remaining=length),decide (remaining=head)⟩ := by
  simp only [remainingPacket, le_refl, ↓reduceIte, packet_at length head remaining anchor within]

theorem remainingPacket_step (length head remaining : ℕ) (anchor : ℤ) :
    Function.update (remainingPacket length head (remaining+1) anchor) (anchor+((remaining+1 : ℕ) : ℤ)) none =
      remainingPacket length head remaining anchor := by
  funext x
  by_cases atEnd : x=anchor+((remaining+1 : ℕ) : ℤ)
  · subst x
    simp only [Function.update_self, remainingPacket]
    rw [if_neg (by omega)]
  · rw [Function.update_of_ne atEnd]
    unfold remainingPacket
    have same : (x≤anchor+((remaining+1 : ℕ) : ℤ)) ↔ x≤anchor+remaining := by omega
    simp only [same]

theorem remainingPacket_zero (length head : ℕ) (anchor : ℤ) :
    Function.update (remainingPacket length head 0 anchor) anchor none = fun _ => none := by
  funext x
  by_cases atStart : x=anchor
  · subst x; simp
  · rw [Function.update_of_ne atStart]
    unfold remainingPacket packet
    split_ifs <;> simp_all <;> omega

theorem clear_packet (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (remaining : ℕ) (within : remaining≤length)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (remainingPacket length head remaining anchor)
      .clearPacket (anchor+remaining) c) :
    ∃ d, State M data fixed source visited (fun _ => none) .cleanupLeft anchor d ∧
      (machine M).Steps data bits c (remaining+1) d ∧ WorkFrame (machine M) c d := by
  induction remaining generalizing c with
  | zero =>
      have mark : (read M (c.work c.workHead)).packet.any IndexMark.first = true := by
        rw [represented.head, represented.memory]
        change (remainingPacket length head 0 anchor (anchor+(0 : ℕ))).any IndexMark.first = true
        rw [remainingPacket_at length head 0 (by omega) anchor]
        simp
      obtain ⟨d, state, path, frame⟩ := represented.packetStep bits .cleanupLeft none .stay (by
        simp only [transition, mark, ↓reduceIte])
      refine ⟨d, ?_, path, frame⟩
      simpa only [Nat.cast_zero, add_zero, Move.onInt, remainingPacket_zero] using state
  | succ remaining ih =>
      have mark : (read M (c.work c.workHead)).packet.any IndexMark.first = false := by
        rw [represented.head, represented.memory]
        change (remainingPacket length head (remaining+1) anchor (anchor+((remaining+1 : ℕ) : ℤ))).any IndexMark.first = false
        rw [remainingPacket_at length head (remaining+1) within anchor]
        simp
      obtain ⟨next, state, step, frame⟩ := represented.packetStep bits .clearPacket none .left (by
        simp only [transition, mark, Bool.false_eq_true, ↓reduceIte])
      have ready : State M data fixed source visited (remainingPacket length head remaining anchor)
          .clearPacket (anchor+remaining) next := by
        rw [remainingPacket_step] at state
        convert state using 1
        simp only [Move.onInt, Nat.cast_add, Nat.cast_one]
        omega
      obtain ⟨d, done, rest, restFrame⟩ := ih (by omega) next ready
      refine ⟨d, done, ?_, frame.trans (machine M) restFrame⟩
      convert step.trans (machine M) rest using 1 <;> omega

theorem cleanup_packet (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (anchor : ℤ) (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) .clearEnd anchor c) :
    ∃ d, State M data fixed source visited (fun _ => none) .cleanupLeft anchor d ∧
      (machine M).Steps data bits c (2*length+2) d ∧ WorkFrame (machine M) c d := by
  obtain ⟨last,lastState,scan,scanFrame⟩ := represented.scan bits length .right (anchor+length)
    (fun t => anchor+t) (by simp) rfl (by intro t _; simp [Move.onInt]; omega) (by
      intro t before input auxiliary index
      rw [machine_transition]
      have mark : (read M (c.work (anchor+t))).packet.any IndexMark.last = false := by
        rw [represented.memory]
        exact Bool.eq_false_iff.mpr ((packet_last_iff length head anchor _).not.mpr (by omega))
      simp only [transition,mark,Bool.false_eq_true,↓reduceIte])
  obtain ⟨next,ready,step,stepFrame⟩ := lastState.silent bits .clearPacket .stay (by
    simp only [transition,lastState.head,lastState.memory (anchor+length),packet_last,↓reduceIte])
  have ready' : State M data fixed source visited (remainingPacket length head length anchor)
      .clearPacket (anchor+length) next := by
    simpa only [remainingPacket_full,Move.onInt] using ready
  obtain ⟨d,done,erase,eraseFrame⟩ := clear_packet M data bits fixed source visited length head anchor length le_rfl next ready'
  refine ⟨d,done,?_,(scanFrame.trans (machine M) stepFrame).trans (machine M) eraseFrame⟩
  convert (scan.trans (machine M) step).trans (machine M) erase using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
