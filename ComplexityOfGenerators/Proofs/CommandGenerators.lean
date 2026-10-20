import ComplexityOfGenerators.Proofs.WordStackGenerators
import ComplexityOfGenerators.Simulation.WordStack.Commands
import ComplexityOfGenerators.Simulation.ClockProgress

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ} [Fintype S] [Fintype O]

abbrev emptyMemory : Memory S O k := ⟨(), 0, 0, [], fun _ => []⟩

theorem Runs.executes (idle : Fin k) {n : ℕ} {bits : BitString} {c : Command S O k}
    {t : ℕ} {result : Result S O k} (run : c.Runs n bits emptyMemory t result) :
    (c.program idle).Executes n bits (c.program idle).initialConfiguration t result.outcome :=
  Program.Evaluates.executes _ (run.compiled idle (Nat.zero_le _))

/-- A finite command implementing a total finite-seed sampler yields a native
polynomial-time generator once its actual primitive cost is bounded. -/
theorem mem_pg (c : Command S O k) (idle : Fin k) (L : Language O) (seed time : PolynomialBound)
    (value : ℕ → BitString → Option (List O))
    (terminates : ∀ n bits, ∃ t result, c.Runs n bits emptyMemory t result ∧ result.outcome.acceptedWord = value n bits)
    (sound : ∀ n bits x, value n bits = some x → x ∈ lengthSlice L n)
    (complete : ∀ n x, x ∈ lengthSlice L n → ∃ bits, bits.length = seed n ∧ value n bits = some x)
    (productive : ∀ n bits, bits.length = seed n → (lengthSlice L n).Nonempty → ∃ x, value n bits = some x)
    (bounded : ∀ n bits, bits.length ≤ seed n → ∃ t ≤ time n, ∃ result, c.Runs n bits emptyMemory t result) :
    L ∈ PG O := by
  let P := c.program idle
  apply P.mem_pg L seed time
  · intro n bits
    obtain ⟨t, result, run, _⟩ := terminates n bits
    exact ⟨t, result.outcome, run.executes idle, by cases result <;> simp [Result.outcome]⟩
  · intro n bits t x output
    obtain ⟨s, result, run, value_eq⟩ := terminates n bits
    obtain ⟨ticks, _, native⟩ := P.run_compiled (run.executes idle)
    obtain ⟨ticks', _, native'⟩ := P.run_compiled output
    have same := P.machine.halted_outcome_unique (generatorData n) bits ticks ticks' _ _ native native'
    apply sound n bits x
    rw [← value_eq, same]
    rfl
  · intro n x member
    obtain ⟨bits, length, output⟩ := complete n x member
    obtain ⟨t, result, run, value_eq⟩ := terminates n bits
    have same : result.outcome = .accepted x := by
      cases result with
      | exhausted => simp [Result.outcome, Outcome.acceptedWord, output] at value_eq
      | done m => simpa [Result.outcome, Outcome.acceptedWord, output] using value_eq
    exact ⟨bits, length, t, same ▸ run.executes idle⟩
  · intro n bits length nonempty
    obtain ⟨x, output⟩ := productive n bits length nonempty
    obtain ⟨t, result, run, value_eq⟩ := terminates n bits
    have same : result.outcome = .accepted x := by
      cases result with
      | exhausted => simp [Result.outcome, Outcome.acceptedWord, output] at value_eq
      | done m => simpa [Result.outcome, Outcome.acceptedWord, output] using value_eq
    exact ⟨t, x, same ▸ run.executes idle⟩
  · intro n bits length
    obtain ⟨t, cost, result, run⟩ := bounded n bits length
    exact ⟨t, cost, result.outcome, run.executes idle⟩

end ComplexityOfGenerators.Simulation.WordStack.Command
