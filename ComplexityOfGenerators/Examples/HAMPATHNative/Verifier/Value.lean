import ComplexityOfGenerators.Examples.HAMPATHSelfReduction

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

structure State where
  current : List Symbol
  remaining : List Symbol

def step (state : State) : State :=
  if state.remaining = [] then state else
    ⟨wordReduce state.current (state.remaining.take (wordWidth state.current)),
      state.remaining.drop (wordWidth state.current)⟩

def baseWord : List Symbol := singleton.encode 0

def accepts (state : State) : Bool := state.remaining.isEmpty && decide (state.current = baseWord)

def value (word certificate : List Symbol) : Bool :=
  accepts (step^[certificate.length] ⟨word, certificate⟩)

theorem step_remaining_length_le (state : State) : (step state).remaining.length ≤ state.remaining.length := by
  by_cases empty : state.remaining = [] <;> simp [step, empty, List.length_drop]

theorem step_current_length_le (state : State) : (step state).current.length ≤ state.current.length := by
  by_cases empty : state.remaining = []
  · simp [step, empty]
  · simpa only [step, ite_eq_right empty] using word_reduce_length state.current (state.remaining.take (wordWidth state.current))

theorem iterate_remaining_length_le (count : ℕ) (state : State) :
    (step^[count] state).remaining.length ≤ state.remaining.length := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (step_remaining_length_le state)

theorem iterate_current_length_le (count : ℕ) (state : State) :
    (step^[count] state).current.length ≤ state.current.length := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (step_current_length_le state)

theorem iterate_empty (count : ℕ) (state : State) (empty : state.remaining = []) :
    step^[count] state = state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply', ih]; simp [step, empty]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
