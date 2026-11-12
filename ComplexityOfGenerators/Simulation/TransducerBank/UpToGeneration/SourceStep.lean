import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceBasic

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

theorem inspect_advance (n : ℕ) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (bounded : source.inputHead ≤ word.length)
    (next : Q) (write : S) (work input : Move) :
    (bank B fallback).advance (generatorData n) (inspecting B fallback word offset source)
      (.commit (B.select source.state) next write work) (wordTape B word source.inputHead)
      (inputMove input (decide ((source.inputHead : ℤ) = 0)) (wordTape B word source.inputHead).2)
      .stay .stay .stay none = committing B fallback word offset source next write work input := by
  have position := inputMove_position B word source.inputHead bounded input
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, inspecting, configuration, committing, bank, generatorData,
      Move.onInput, Nat.zero_min, Option.toList_none, List.append_nil]
  · rw [Fin.lastCases_last, position, Fuel.lastCases_update_last]
    rfl
  · rw [Fin.lastCases_last, Fin.lastCases_last, Function.update_eq_self,
      Fuel.lastCases_update_last]

theorem commit_advance (n : ℕ) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (next : Q) (write : S)
    (work input auxiliary index : Move) (emit : Option Unit) :
    (bank B fallback).advance (generatorData n)
      (committing B fallback word offset source next write work input)
      (.fetch next) (write, none) work .stay .stay .stay none =
      configuration B fallback word offset
        (B.advance (decisionData word) source next write work input auxiliary index emit) := by
  have distinct : Fin.last k ≠ (B.select source.state).castSucc :=
    Ne.symm (Fin.ne_of_lt (B.select source.state).castSucc_lt_last)
  apply BankConfiguration.ext <;>
    simp only [TapeBank.advance, committing, configuration, bank, generatorData, decisionData,
      Move.onInput, Nat.zero_min, Option.toList_none, List.append_nil]
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

/-- Each source instruction is replayed on real separate source/input tapes. -/
theorem step_path (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (bounded : source.inputHead ≤ word.length)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option Unit)
    (action : B.instruction (decisionData word) source = .step next write work input auxiliary index emit) :
    (bank B fallback).Steps (generatorData n) bits (configuration B fallback word offset source) 3
      (configuration B fallback word offset
        (B.advance (decisionData word) source next write work input auxiliary index emit)) := by
  have first := fetch_step B fallback n bits word offset source
  have second : (bank B fallback).Steps (generatorData n) bits
      (inspecting B fallback word offset source) 1
      (committing B fallback word offset source next write work input) := by
    have instruction := inspect_instruction B fallback n word offset source
    rw [action] at instruction
    have actual := TapeBank.Steps.single (bank B fallback) (generatorData n) bits _ _ _ _ _ _ _ _ instruction
    simpa only [inspect_advance B fallback n word offset source bounded] using actual
  have third : (bank B fallback).Steps (generatorData n) bits
      (committing B fallback word offset source next write work input) 1
      (configuration B fallback word offset
        (B.advance (decisionData word) source next write work input auxiliary index emit)) := by
    have instruction : (bank B fallback).instruction (generatorData n)
        (committing B fallback word offset source next write work input) =
        .step (.fetch next) (write, none) work .stay .stay .stay none := by
      simp [TapeBank.instruction, committing, bank]
    have actual := TapeBank.Steps.single (bank B fallback) (generatorData n) bits _ _ _ _ _ _ _ _ instruction
    simpa only [commit_advance B fallback n word offset source next write work input auxiliary index emit]
      using actual
  exact (first.trans (bank B fallback) second).trans (bank B fallback) third

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
