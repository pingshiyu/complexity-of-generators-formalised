import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ}
  (B : TapeBank I A O Q S k)

/-- A source-state lookup only reads the source tape and caches finite data. -/
theorem fetch_instruction (data : InputData I A) (fuel used : ℕ)
    (source : BankConfiguration O Q S k) :
    (bank B).instruction data (configuration B fuel used source) =
      match B.instruction data source with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes => .step (.tickRandom no yes)
          (.inl (source.tape (B.select source.state) (source.head (B.select source.state))))
          .stay .stay .stay .stay none
      | .step next write work input auxiliary index emit =>
          .step (.tickStep (B.select source.state) next write work input auxiliary index emit)
            (.inl (source.tape (B.select source.state) (source.head (B.select source.state))))
            .stay .stay .stay .stay none := by
  simp [TapeBank.instruction, bank, configuration, readSource]
  rfl

/-- Update laws for the actual extra clock tape, with all source tapes framed. -/
theorem lastCases_update_last {α : Type} (last : α) (values : Fin k → α) (new : α) :
    Function.update (Fin.lastCases (motive := fun _ : Fin (k + 1) => α) last values) (Fin.last k) new = Fin.lastCases (motive := fun _ : Fin (k + 1) => α) new values := by
  classical
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem lastCases_update_castSucc {α : Type} (last : α) (values : Fin k → α)
    (selected : Fin k) (new : α) :
    Function.update (Fin.lastCases (motive := fun _ : Fin (k + 1) => α) last values) selected.castSucc new =
      Fin.lastCases (motive := fun _ : Fin (k + 1) => α) last (Function.update values selected new) := by
  classical
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [Function.update_of_ne (Ne.symm (Fin.ne_of_lt selected.castSucc_lt_last))]
  · by_cases same : j = selected
    · subst j; simp
    · simp [same, Function.update_of_ne]

/-- Advancing the clock cursor costs one real transition and never changes its
contents, a source head, an external head, randomness, or accumulated output. -/
theorem clock_advance (data : InputData I A) (fuel used : ℕ)
    (source : BankConfiguration O Q S k) (phase next : Phase Q S O k)
    (clockSelected : (bank B).select phase = Fin.last k)
    (inputBound : source.inputHead ≤ data.input.length)
    (auxiliaryBound : source.auxiliaryHead ≤ data.auxiliary.length)
    (indexBound : source.indexHead ≤ data.index) :
    (bank B).advance data {configuration B fuel used source with state := phase} next
      (clockTape B fuel used) .right .stay .stay .stay none =
      {configuration B fuel (used + 1) source with state := next} := by
  have clockHead : (configuration B fuel used source).head (Fin.last k) = (used : ℤ) := by
    simp [configuration]
  have clockCell : (configuration B fuel used source).tape (Fin.last k)
      ((configuration B fuel used source).head (Fin.last k)) = clockTape B fuel used := by
    simp [configuration]
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, configuration, clockSelected, Move.onInput,
      Nat.min_eq_left inputBound, Nat.min_eq_left auxiliaryBound,
      Nat.min_eq_left indexBound, Option.toList_none, List.append_nil]
  · rw [Fin.lastCases_last, Move.onInt, lastCases_update_last]
    congr 1
  · rw [Fin.lastCases_last, Fin.lastCases_last, Function.update_eq_self,
      lastCases_update_last]

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
