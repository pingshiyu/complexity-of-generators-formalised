import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.Step
import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

def committing (data : InputData I A) (source : BankConfiguration O Q S k)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O) :
    BankConfiguration O (Phase Q S k) (Cell (S := S)) (k + 1) :=
  {configuration B data source with
    state := .commit (B.select source.state) next write work
    inputHead := input.onInput data.input.length source.inputHead
    auxiliaryHead := auxiliary.onInput data.auxiliary.length source.auxiliaryHead
    output := source.output ++ emit.toList
    head := Fin.lastCases (index.onInput data.input.length source.indexHead : ℤ) source.head}

theorem inspect_advance (data : InputData I A) (r : ℕ) (source : BankConfiguration O Q S k)
    (bounds : B.Bounded (sourceData data) r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O) :
    (bank B).advance data (inspecting B data source)
      (.commit (B.select source.state) next write work)
      (indexTape B data.input.length source.indexHead)
      (indexMove index (decide ((source.indexHead : ℤ) = 0))
        (indexTape B data.input.length source.indexHead)) input auxiliary .stay emit =
      committing B data source next write work input auxiliary index emit := by
  have position := indexMove_position B data.input.length source.indexHead bounds.index index
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, inspecting, configuration, committing, bank,
      Move.onInput, Nat.zero_min]
  · rw [Fin.lastCases_last, position, Fuel.lastCases_update_last]
    rfl
  · rw [Fin.lastCases_last, Fin.lastCases_last, Function.update_eq_self,
      Fuel.lastCases_update_last]

theorem commit_advance (data : InputData I A) (r : ℕ) (source : BankConfiguration O Q S k)
    (bounds : B.Bounded (sourceData data) r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O) :
    (bank B).advance data (committing B data source next write work input auxiliary index emit)
      (.fetch next) (.inl write) work .stay .stay .stay none =
      configuration B data
        (B.advance (sourceData data) source next write work input auxiliary index emit) := by
  have inputBound := input.onInput_le data.input.length source.inputHead bounds.input
  have auxiliaryBound := auxiliary.onInput_le data.auxiliary.length source.auxiliaryHead bounds.auxiliary
  simp only [Move.onInput] at inputBound auxiliaryBound
  have distinct : Fin.last k ≠ (B.select source.state).castSucc :=
    Ne.symm (Fin.ne_of_lt (B.select source.state).castSucc_lt_last)
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, committing, configuration, bank, sourceData, Move.onInput,
      Nat.min_eq_left inputBound, Nat.min_eq_left auxiliaryBound, Nat.zero_min,
      Option.toList_none, List.append_nil]
  · funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Function.update_apply, distinct]
    · by_cases same : j = B.select source.state
      · subst j; simp [Function.update_apply]
      · simp [Function.update_apply, same]
  · funext j p
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Function.update_apply, distinct]
    · by_cases same : j = B.select source.state
      · subst j
        by_cases location : p = source.head (B.select source.state) <;>
          simp [Function.update_apply, location]
      · simp [Function.update_apply, same]

/-- One source transition is a work lookup, a real unary-index access, and a
work commit. It never scans the source work bank. -/
theorem step_path (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded (sourceData data) r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O)
    (action : B.instruction (sourceData data) source = .step next write work input auxiliary index emit) :
    (bank B).Steps data bits (configuration B data source) 3
      (configuration B data (B.advance (sourceData data) source
        next write work input auxiliary index emit)) := by
  have first := fetch_step B data bits r source bounds
  have second : (bank B).Steps data bits (inspecting B data source) 1
      (committing B data source next write work input auxiliary index emit) := by
    have instruction := inspect_instruction B data source
    rw [action] at instruction
    have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
    simpa only [inspect_advance B data r source bounds] using actual
  have third : (bank B).Steps data bits
      (committing B data source next write work input auxiliary index emit) 1
      (configuration B data (B.advance (sourceData data) source
        next write work input auxiliary index emit)) := by
    have instruction : (bank B).instruction data
        (committing B data source next write work input auxiliary index emit) =
        .step (.fetch next) (.inl write) work .stay .stay .stay none := by
      simp [TapeBank.instruction, committing, bank]
    have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
    simpa only [commit_advance B data r source bounds] using actual
  exact (first.trans (bank B) second).trans (bank B) third

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
