import ComplexityOfGenerators.Simulation.WordStack.Source
import ComplexityOfGenerators.Simulation.WordStack.LocalZipper

namespace ComplexityOfGenerators.Simulation.WordStack.Source

variable {I A O : Type} (M : Machine I A O)

namespace Snapshot

theorem write_state (c : Snapshot M) (q : Status (Fin M.states)) :
    (Local.write 0 (.state q)).eval (c.store M) = ({c with status := q}).store M := by
  rw [Local.eval_write]
  funext j
  fin_cases j <;> simp [store]

theorem pop_random (c : Snapshot M) :
    (Local.pop 9).eval (c.store M) = ({c with random := c.random.tail}).store M := by
  rw [Local.eval_pop]
  funext j
  fin_cases j <;> simp [store, List.map_tail]

theorem push_output (c : Snapshot M) (a : O) :
    (Local.push 10 (.output a)).eval (c.store M) = ({c with output := a :: c.output}).store M := by
  rw [Local.eval_push]
  funext j
  fin_cases j <;> simp [store]

theorem write_work (c : Snapshot M) (a : Option (Fin M.symbols)) :
    (Local.write 8 (.work a)).eval (c.store M) = ({c with work := c.work.write a}).store M := by
  rw [Local.eval_write]
  funext j
  fin_cases j <;> simp [store, Zipper.write, List.map_tail]

theorem move_input (c : Snapshot M) (dir : Move) :
    (Local.moveRead 1 2 dir).eval (c.store M) =
      ({c with input := c.input.clampedMove dir}).store M := by
  rw [Local.eval_moveRead 1 2 (by decide)]
  change Function.update (Function.update (c.store M) 1
    ((c.input.map Cell.input).clampedMove dir).left) 2
    ((c.input.map Cell.input).clampedMove dir).right = _
  rw [Zipper.map_clampedMove]
  funext j
  fin_cases j <;> simp [store, Zipper.map]

theorem move_auxiliary (c : Snapshot M) (dir : Move) :
    (Local.moveRead 3 4 dir).eval (c.store M) =
      ({c with auxiliary := c.auxiliary.clampedMove dir}).store M := by
  rw [Local.eval_moveRead 3 4 (by decide)]
  change Function.update (Function.update (c.store M) 3
    ((c.auxiliary.map Cell.auxiliary).clampedMove dir).left) 4
    ((c.auxiliary.map Cell.auxiliary).clampedMove dir).right = _
  rw [Zipper.map_clampedMove]
  funext j
  fin_cases j <;> simp [store, Zipper.map]

theorem move_index (c : Snapshot M) (dir : Move) :
    (Local.moveRead 5 6 dir).eval (c.store M) =
      ({c with index := c.index.clampedMove dir}).store M := by
  rw [Local.eval_moveRead 5 6 (by decide)]
  change Function.update (Function.update (c.store M) 5
    ((c.index.map (fun _ => Cell.unit)).clampedMove dir).left) 6
    ((c.index.map (fun _ => Cell.unit)).clampedMove dir).right = _
  rw [Zipper.map_clampedMove]
  funext j
  fin_cases j <;> simp [store, Zipper.map]

theorem move_work (c : Snapshot M) (dir : Move) :
    (Local.moveWork 7 8 (.work none) dir).eval (c.store M) =
      ({c with work := c.work.workMove none dir}).store M := by
  rw [Local.eval_moveWork 7 8 (by decide)]
  change Function.update (Function.update (c.store M) 7
    ((c.work.map Cell.work).workMove (Cell.work none) dir).left) 8
    ((c.work.map Cell.work).workMove (Cell.work none) dir).right = _
  rw [Zipper.map_workMove]
  funext j
  fin_cases j <;> simp [store, Zipper.map]

@[simp] theorem read_state (c : Snapshot M) : Cell.getState M ((c.store M 0).head?) = c.status := rfl
@[simp] theorem read_input (c : Snapshot M) : Cell.getInput M ((c.store M 2).head?) = c.input.read := by
  cases h : c.input.right <;> simp [store, Zipper.read, h, Cell.getInput]
@[simp] theorem read_auxiliary (c : Snapshot M) : Cell.getAuxiliary M ((c.store M 4).head?) = c.auxiliary.read := by
  cases h : c.auxiliary.right <;> simp [store, Zipper.read, h, Cell.getAuxiliary]
@[simp] theorem read_index (c : Snapshot M) : Cell.getIndex M ((c.store M 6).head?) = c.index.read := by
  cases h : c.index.right with
  | nil => simp [store, Zipper.read, h, Cell.getIndex]
  | cons a rest => cases a; simp [store, Zipper.read, h, Cell.getIndex]
@[simp] theorem read_work (c : Snapshot M) : Cell.getWork M ((c.store M 8).head?) = c.work.read.getD none := by
  cases h : c.work.right <;> simp [store, Zipper.read, h, Cell.getWork]
@[simp] theorem read_bit (c : Snapshot M) : Cell.getBit M ((c.store M 9).head?) = c.random.head? := by
  cases h : c.random <;> simp [store, h, Cell.getBit]

end Snapshot

/-- One native instruction is implemented using only a bounded number of
single-symbol stack instructions. -/
theorem step_eval (c : Snapshot M) : (step M).eval (c.store M) = (c.step M).store M := by
  simp only [step, Local.eval_read, Snapshot.read_state]
  cases state : c.status with
  | accepted => simp [Snapshot.step, state]
  | rejected => simp [Snapshot.step, state]
  | exhausted => simp [Snapshot.step, state]
  | live q =>
    simp only [Local.eval_read, Snapshot.read_input, Snapshot.read_auxiliary,
      Snapshot.read_index, Snapshot.read_work, Snapshot.step, state]
    cases action : M.transition q c.input.read c.auxiliary.read c.index.read (c.work.read.getD none) with
    | accept => exact c.write_state M .accepted
    | reject => exact c.write_state M .rejected
    | readRandom no yes =>
      simp only [execute, Local.eval_read, Snapshot.read_bit]
      cases random : c.random with
      | nil => simpa [random] using c.write_state M .exhausted
      | cons b rest =>
        simp only [List.head?_cons, Local.eval_seq, Snapshot.pop_random, Snapshot.write_state]
        simp only [random, List.tail_cons]
    | step q w wm im am nm emit =>
      cases w <;> cases emit <;>
        simp only [execute, Local.eval_seq, Snapshot.write_state, Snapshot.move_input,
          Snapshot.move_auxiliary, Snapshot.move_index, Snapshot.write_work, Snapshot.move_work,
          Snapshot.push_output, Local.eval_skip]

end ComplexityOfGenerators.Simulation.WordStack.Source
