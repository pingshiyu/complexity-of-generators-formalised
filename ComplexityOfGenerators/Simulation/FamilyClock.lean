import ComplexityOfGenerators.Simulation.PolynomialClockCorrectness
import ComplexityOfGenerators.Simulation.UnaryInput
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

/-!
# A polynomial clock driven by the physical family index

Swapping unary input and index before and after the verified clock compiler
provides a blank-tape clock for uniform generator families. Empty slices may
reach the deadline and explicitly reject. The composition construction can
route that rejection to exhaustion; no unbounded sampler call is hidden in it.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O) (p : PolynomialBound)

def familyClock : Machine Unit Bool O :=
  unarySwapMachine (polynomialClockMachine (unarySwapMachine M) p)

theorem familyClock_timeBound (n : ℕ) :
    (familyClock M p).TimeBound (generatorData n) (polynomialClockTime p n) := by
  have bound := unarySwap_timeBound (polynomialClockMachine (unarySwapMachine M) p)
    (decisionData (List.replicate n ())) (polynomialClockTime p n)
    (by simpa using polynomialClockMachine_timeBound (unarySwapMachine M) p (List.replicate n ()))
  simpa only [familyClock, unarySwap_decisionData] using bound

theorem familyClock_produces_iff (n : ℕ) (bits : BitString) (word : List O) :
    (familyClock M p).Produces (generatorData n) bits word ↔
      M.run (generatorData n) bits (p (n + 1)) = .halted (.accepted word) := by
  have swap := unarySwap_produces_iff (polynomialClockMachine (unarySwapMachine M) p)
    (decisionData (List.replicate n ())) bits word
  rw [unarySwap_decisionData] at swap
  rw [show familyClock M p = unarySwapMachine (polynomialClockMachine (unarySwapMachine M) p) from rfl,
    swap, polynomialClockMachine_produces_iff]
  have data : unarySwapData (generatorData n) = decisionData (List.replicate n ()) := by
    simp [unarySwapData, generatorData, decisionData]
  rw [List.length_replicate, ← data, unarySwap_run]
  cases M.run (generatorData n) bits (p (n + 1)) with
  | running c => simp [unarySwapResult]
  | halted result => simp [unarySwapResult]

/-- Clocking preserves every source output on its original random tape when
the source has a Remark 1 bound. Empty slices remain empty. -/
theorem familyClock_preserves (n seed : ℕ)
    (bound : M.GeneratorTimeBound (generatorData n) seed (p n))
    (bits : BitString) (word : List O) :
    (familyClock M p).Produces (generatorData n) bits word ↔ M.Produces (generatorData n) bits word := by
  rw [familyClock_produces_iff]
  constructor
  · intro accepted
    exact ⟨_, accepted⟩
  · intro produced
    have nonempty : (M.generatedLanguage (generatorData n)).Nonempty :=
      ⟨word, bits ++ [false], by simp, M.produces_append _ bits [false] word produced⟩
    have total := M.generatorTimeBound_timeBound_of_nonempty _ seed (p n) bound nonempty
    have later := M.timeBound_mono _ (p.monotone (Nat.le_succ n)) total
    exact M.produces_at_bound _ bits (p (n + 1)) word (later bits) produced

/-- The output-language form of `familyClock_preserves`, for composing the
clocked sampler with a subsequent machine. -/
theorem familyClock_generatedLanguage (n seed : ℕ)
    (bound : M.GeneratorTimeBound (generatorData n) seed (p n)) :
    (familyClock M p).generatedLanguage (generatorData n) =
      M.generatedLanguage (generatorData n) := by
  ext word
  simp only [Machine.generatedLanguage, Set.mem_setOf_eq,
    familyClock_preserves M p n seed bound]

end
end ComplexityOfGenerators.Simulation
