import ComplexityOfGenerators.Foundations.RandomTape

/-! Prefixing a random tape and shifting its cursor changes no computation.
This lets finite transcript paths be realised by ordinary native choice tapes. -/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

def shiftRandomConfiguration (lead : BitString) (c : Configuration M) : Configuration M :=
  {c with randomHead := lead.length + c.randomHead}

def shiftRandomResult (lead : BitString) : RunState M → RunState M
  | .running c => .running (M.shiftRandomConfiguration lead c)
  | .halted result => .halted result

theorem observe_shift_random (data : InputData I A) (lead bits : BitString) (c : Configuration M) :
    M.observe data (lead ++ bits) (M.shiftRandomConfiguration lead c) =
      M.shiftRandomResult lead (M.observe data bits c) := by
  unfold observe shiftRandomConfiguration
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) <;>
    simp only [shiftRandomResult, shiftRandomConfiguration, List.length_append, Nat.add_lt_add_iff_left]
  split_ifs <;> rfl

theorem next_shift_random (data : InputData I A) (lead bits : BitString) (c : Configuration M) :
    M.next data (lead ++ bits) (M.shiftRandomConfiguration lead c) =
      M.shiftRandomResult lead (M.next data bits c) := by
  unfold next shiftRandomConfiguration
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | step state write work input auxiliary index emit => rfl
  | readRandom no yes =>
      rw [List.getElem?_append_right (by change lead.length ≤ lead.length + c.randomHead; omega)]
      simp only [Nat.add_sub_cancel_left]
      cases bits[c.randomHead]? with
      | none => rfl
      | some bit => simp [shiftRandomResult, shiftRandomConfiguration, Nat.add_assoc]

theorem runFrom_shift_random (data : InputData I A) (lead bits : BitString) (c : Configuration M) (t : ℕ) :
    M.runFrom data (lead ++ bits) (M.shiftRandomConfiguration lead c) t =
      M.shiftRandomResult lead (M.runFrom data bits c t) := by
  induction t with
  | zero => exact M.observe_shift_random data lead bits c
  | succ t ih =>
      rw [runFrom, ih, runFrom]
      cases M.runFrom data bits c t with
      | halted result => rfl
      | running d =>
          simp only [shiftRandomResult]
          rw [M.next_shift_random data lead bits d]
          cases M.next data bits d with
          | halted result => rfl
          | running next => exact M.observe_shift_random data lead bits next

end ComplexityOfGenerators.Machine
