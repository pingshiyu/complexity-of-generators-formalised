import ComplexityOfGenerators.Simulation.NativeSourceCall.IndexStep

/-! Native rejection and finite-random-tape exhaustion are preserved without
running any unbounded cleanup. Accepting calls use the separate cleanup path. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem fetch_table (data : InputData Unit Bool)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (q : Fin M.states)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.fetch q (source anchor)) (anchor+head) c) :
    transition M (.fetch q (source anchor)) (c.work c.workHead) =
      match M.transition q none none (if head<length then some () else none) (source anchor) with
      | .accept => .step (control M (.returning .accepted)) none .stay .stay .stay .stay none
      | .reject => .reject
      | .readRandom no yes => .readRandom (control M (.returning (.resume no))) (control M (.returning (.resume yes)))
      | .step next write work _ _ index emit => .step (control M (.placeIndex ⟨next,write,work,emit⟩))
          (some (alphabet M {read M (c.work c.workHead) with
            packet := some {mark length head head with head:=false}}))
          (indexMove (mark length head head) index) .stay .stay .stay none := by
  have currentPacket : (read M (c.work c.workHead)).packet=some (mark length head head) := by
    rw [represented.head,represented.memory]
    exact packet_at_mark length head head anchor within
  simp only [transition,currentPacket,mark,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [show (if decide (head=length) then (none : Option Unit) else some ()) =
    (if head<length then some () else none) by simpa only [mark] using index_symbol length head within]
  rfl

theorem rejected (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (q : Fin M.states)
    (sourceTable : M.transition q none none (if head<length then some () else none) (source anchor)=.reject)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.source q) anchor c) :
    (machine M).runFrom data bits c (head+1)=.halted .rejected := by
  obtain ⟨fetched,state,path,frame⟩ := fetch M data bits fixed source visited length head within anchor q c represented
  rw [path.runFrom (machine M)]
  have table := fetch_table M data fixed source visited length head within anchor q fetched state
  rw [sourceTable] at table
  simp only [Machine.observe,state.state,machine_transition,table]

theorem exhausted (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (length head : ℕ) (within : head≤length) (anchor : ℤ) (q no yes : Fin M.states)
    (sourceTable : M.transition q none none (if head<length then some () else none) (source anchor)=.readRandom no yes)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited (packet length head anchor) (.source q) anchor c)
    (absent : bits[c.randomHead]?=none) :
    (machine M).runFrom data bits c (head+1)=.halted .exhausted := by
  obtain ⟨fetched,state,path,frame⟩ := fetch M data bits fixed source visited length head within anchor q c represented
  rw [path.runFrom (machine M)]
  have table := fetch_table M data fixed source visited length head within anchor q fetched state
  rw [sourceTable] at table
  have missing : ¬fetched.randomHead<bits.length := by
    rw [frame.random]
    exact Nat.not_lt_of_ge (List.getElem?_eq_none_iff.mp absent)
  simp only [Machine.observe,state.state,machine_transition,table,missing,↓reduceIte]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
