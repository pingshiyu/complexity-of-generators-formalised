import ComplexityOfGenerators.Foundations.ExecutionPaths

/-! A clocked evaluator which charges terminal lookup as one extra instruction.
It is convenient for interpreters whose clock is stored on a work stack. -/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

def rawTick (data : InputData I A) (bits : BitString) : RunState M → RunState M
  | .halted result => .halted result
  | .running c => M.next data bits c

def rawRun (data : InputData I A) (bits : BitString) (start : RunState M) (t : ℕ) : RunState M :=
  (M.rawTick data bits)^[t] start

theorem observe_halted_iff_next (data : InputData I A) (bits : BitString)
    (c : Configuration M) (result : Outcome O) :
    M.observe data bits c = .halted result ↔ M.next data bits c = .halted result := by
  unfold observe next
  split
  · rfl
  · rfl
  · rename_i no yes action
    by_cases available : c.randomHead < bits.length
    · simp [available, List.getElem?_eq_getElem available]
    · have absent : bits[c.randomHead]? = none := List.getElem?_eq_none (by omega)
      simp [available, absent]
  · simp

theorem rawRun_halted (data : InputData I A) (bits : BitString) (result : Outcome O) (t : ℕ) :
    M.rawRun data bits (.halted result) t = .halted result := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [rawRun, Function.iterate_succ_apply]
    exact ih

theorem rawRun_correct (data : InputData I A) (bits : BitString)
    (c : Configuration M) (t : ℕ) (result : Outcome O) :
    M.rawRun data bits (.running c) (t + 1) = .halted result ↔
      M.runFrom data bits c t = .halted result := by
  induction t generalizing c with
  | zero => exact (M.observe_halted_iff_next data bits c result).symm
  | succ t ih =>
    rw [rawRun, Function.iterate_succ_apply]
    change M.rawRun data bits (M.next data bits c) (t + 1) = .halted result ↔ _
    cases step : M.next data bits c with
    | halted out =>
      have terminal := (M.observe_halted_iff_next data bits c out).mpr step
      rw [M.rawRun_halted, M.runFrom_halted data bits c out terminal]
    | running d =>
      rw [ih d, M.runFrom_shift data bits c d (M.observe_of_next_running data bits c d step) step]

end ComplexityOfGenerators.Machine
