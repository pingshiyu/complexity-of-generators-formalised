import ComplexityOfGenerators.Proofs.CommandGenerators
import ComplexityOfGenerators.Simulation.UnionGenerator.Components

/-! Reuse a checked finite command as a bounded source phase. Its actual native
compiler supplies both the execution clock and the optional output law. -/
namespace ComplexityOfGenerators.Simulation.WordStack.Command
noncomputable section
variable {S O : Type} {k : ℕ} [Fintype S] [Fintype O]

theorem bounded_sourceValue (code : Command S O k) (idle : Fin k)
    (seed time : PolynomialBound) (value : ℕ → BitString → Option (List O))
    (computes : ∀ n bits, ∃ t result, code.Runs n bits emptyMemory t result ∧ result.outcome.acceptedWord = value n bits)
    (bounded : ∀ n bits, bits.length ≤ seed n → ∃ t ≤ time n, ∃ result, code.Runs n bits emptyMemory t result)
    (n : ℕ) (bits : BitString) (short : bits.length ≤ seed n) :
    UnionGenerator.sourceValue (code.program idle).machine (Program.compiledTime time) n bits = value n bits := by
  let P := code.program idle
  obtain ⟨ticks, cost, result, run⟩ := bounded n bits short
  obtain ⟨nativeTicks, nativeCost, native⟩ := P.run_compiled (run.executes idle)
  have later := nativeCost.trans (Program.compiledTime_bound time n ticks cost)
  have padded := P.machine.run_halted_add (generatorData n) bits nativeTicks result.outcome native
    (Program.compiledTime time n-nativeTicks)
  rw [Nat.add_sub_of_le later] at padded
  obtain ⟨referenceTicks, referenceResult, referenceRun, answer⟩ := computes n bits
  obtain ⟨referenceNativeTicks, _, referenceNative⟩ := P.run_compiled (referenceRun.executes idle)
  have same := P.machine.halted_outcome_unique (generatorData n) bits nativeTicks referenceNativeTicks _ _ native referenceNative
  change (P.machine.run (generatorData n) bits (Program.compiledTime time n)).acceptedWord = _
  rw [padded]
  simpa only [RunState.acceptedWord, same] using answer

end
end ComplexityOfGenerators.Simulation.WordStack.Command
