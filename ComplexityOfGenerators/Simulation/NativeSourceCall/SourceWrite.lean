import ComplexityOfGenerators.Simulation.NativeSourceCall.State

/-! Source work symbols remain at their original physical coordinates; source
outputs go directly to the native output tape with any existing prefix. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

def afterExecute (action : Action O M.states M.symbols) : Phase O M.states M.symbols :=
  match action.move with
  | .stay => .source action.next
  | .right => .rightBegin action.next
  | .left => .leftEnd action.next

theorem source_write (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (block : ℤ → Option IndexMark) (anchor : ℤ) (action : Action O M.states M.symbols)
    (c : Configuration (machine (F := F) M))
    (represented : State M data fixed source visited block (.execute action) anchor c) :
    ∃ d, State M data fixed (Function.update source anchor (action.write.or (source anchor)))
        visited block (afterExecute M action) anchor d ∧
      (machine M).Steps data bits c 1 d ∧ d.randomHead=c.randomHead ∧
      d.inputHead=c.inputHead ∧ d.auxiliaryHead=c.auxiliaryHead ∧ d.indexHead=c.indexHead ∧
      d.output=c.output++action.emit.toList := by
  let cell := {read M (c.work c.workHead) with source := action.write.or (source anchor)}
  let d := advance M data c (afterExecute M action) (some cell) .stay action.emit
  have table : transition M (.execute action) (c.work c.workHead) =
      .step (control M (afterExecute M action)) (some (alphabet M cell))
        .stay .stay .stay .stay action.emit := by
    simp only [transition, afterExecute, cell, represented.head, represented.memory anchor]
    rfl
  refine ⟨d, ⟨?_, rfl, ?_, advance_bounds M data c _ _ _ _ represented.bounds⟩,
    advance_path M data bits c (.execute action) _ (some cell) .stay action.emit represented.state table,
    rfl, Nat.min_eq_left represented.bounds.input, Nat.min_eq_left represented.bounds.auxiliary,
    Nat.min_eq_left represented.bounds.index, ?_⟩
  · change Memory M fixed (Function.update source anchor (action.write.or (source anchor))) visited block
      (Function.update c.work c.workHead (some (alphabet M cell)))
    dsimp only [cell]
    rw [represented.head]
    exact represented.memory.source_write M anchor (action.write.or (source anchor))
  · simpa only [d, advance_head, represented.head, Move.onInt]
  · cases emitted : action.emit <;> simp [d, advance, Machine.stepConfiguration, emitted]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
