import ComplexityOfGenerators.Simulation.TransducerBank.RandomTape
import ComplexityOfGenerators.MultitapeModel

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- An accepted run never inspects random bits beyond its finite choice tape. -/
theorem Executes.append_accepted {data : InputData I A} {bits : BitString}
    {source : BankConfiguration O Q S k} {ticks : ℕ} {word : Word O}
    (execution : B.Executes data bits source ticks (.accepted word)) (suffix : BitString) :
    B.Executes data (bits ++ suffix) source ticks (.accepted word) := by
  induction ticks generalizing source with
  | zero =>
      cases execution with
      | accept source table => exact .accept source table
  | succ ticks ih =>
      cases execution with
      | random source no yes bit ticks result table lookup rest =>
          have available := (List.getElem?_eq_some_iff.mp lookup).1
          have newLookup : (bits ++ suffix)[source.randomHead]? = some bit := by
            rw [List.getElem?_append_left available]
            exact lookup
          exact .random source no yes bit ticks (.accepted word) table newLookup (ih rest)
      | step source next write work input auxiliary index emit ticks result table rest =>
          exact .step source next write work input auxiliary index emit ticks (.accepted word)
            table (ih rest)

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

namespace ComplexityOfGenerators.MultitapeMachine

variable {I A O : Type} (M : MultitapeMachine I A O)

theorem produces_append (data : InputData I A) (bits suffix : BitString) (word : Word O)
    (produced : M.Produces data bits word) : M.Produces data (bits ++ suffix) word := by
  obtain ⟨ticks, execution⟩ := produced
  exact ⟨ticks, execution.append_accepted M.program suffix⟩

theorem generatedLanguage_iff_produces (data : InputData I A) (word : Word O) :
    word ∈ M.generatedLanguage data ↔ ∃ bits, M.Produces data bits word := by
  constructor
  · rintro ⟨bits, _, produced⟩
    exact ⟨bits, produced⟩
  · rintro ⟨bits, produced⟩
    exact ⟨bits ++ [false], by simp, M.produces_append data bits [false] word produced⟩

end ComplexityOfGenerators.MultitapeMachine
