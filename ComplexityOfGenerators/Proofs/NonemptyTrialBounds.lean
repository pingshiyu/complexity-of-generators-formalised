import ComplexityOfGenerators.Proofs.CryptographicReduction
import ComplexityOfGenerators.Foundations.ExecutionBounds

/-!
# Ordinary time bounds on nonempty generator slices

The collision reduction uses only nonempty slices. On such slices the Remark 1
trial bound implies a time bound on every finite random tape, including tapes
longer than the trial budget. No artificial clock or restriction of the
attacker's random tapes is needed for this part of the reduction.
-/

namespace ComplexityOfGenerators

namespace Machine

variable {I A O : Type} (M : Machine I A O)

/-- Halting persists when the allowed transition budget is increased. -/
theorem haltsWithin_mono (data : InputData I A) (bits : BitString) {s t : ℕ}
    (bound : s ≤ t) (halted : M.HaltsWithin data bits s) : M.HaltsWithin data bits t := by
  obtain ⟨result, execution⟩ := halted
  exact ⟨result, by simpa [Nat.add_sub_of_le bound] using
    M.run_halted_add data bits s result execution (t - s)⟩

theorem timeBound_mono (data : InputData I A) {s t : ℕ}
    (bound : s ≤ t) (halted : M.TimeBound data s) : M.TimeBound data t :=
  fun bits => M.haltsWithin_mono data bits bound (halted bits)

/-- A halting generator accepts every tape longer than its execution budget:
there are too few transitions to exhaust that tape, and explicit rejection is
excluded by the generator definition. This is useful when a simulator's choice
tape supplies more than the original trial's minimum number of random bits. -/
theorem accepts_at_timeBound_of_long_tape (data : InputData I A) (t : ℕ)
    (generator : M.IsGenerator data) (bound : M.TimeBound data t)
    (bits : BitString) (long : t < bits.length) :
    ∃ word, M.run data bits t = .halted (.accepted word) := by
  obtain ⟨outcome, execution⟩ := bound bits
  cases outcome with
  | accepted word => exact ⟨word, execution⟩
  | rejected => exact False.elim (generator.1.2 bits t execution)
  | exhausted => exact False.elim (M.run_not_exhausted_of_length data bits t long execution)

/-- Full-budget acceptance prevents longer random tapes from delaying a run. -/
theorem generatorTimeBound_timeBound_of_nonempty (data : InputData I A) (seed t : ℕ)
    (bound : M.GeneratorTimeBound data seed t)
    (nonempty : (M.generatedLanguage data).Nonempty) : M.TimeBound data t := by
  intro bits
  by_cases short : bits.length ≤ seed
  · exact bound.1 bits short
  · have length : (bits.take seed).length = seed := by simp [List.length_take]; omega
    obtain ⟨word, produces⟩ := (bound.2 (bits.take seed) length).mpr nonempty
    have accepted := M.produces_at_bound data (bits.take seed) t word
      (bound.1 (bits.take seed) length.le) produces
    have extension := M.run_append_of_not_exhausted data (bits.take seed) (bits.drop seed) t (by simp [accepted])
    rw [List.take_append_drop] at extension
    exact ⟨.accepted word, extension.trans accepted⟩

end Machine

/-- Every collision slice used by the attack has an ordinary all-tapes time
bound, not merely a bound for truncated trials. -/
theorem HashFunction.collision_generator_timeBound (h : HashFunction)
    (G : GeneratorFamily PairSymbol)
    (language : G.toUniformGenerators.language = h.collisionLanguage)
    (seed p : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed p) (n : ℕ) :
    G.machine.TimeBound (generatorData (2 * (n + 1) + 1)) (p (2 * (n + 1) + 1)) := by
  apply G.machine.generatorTimeBound_timeBound_of_nonempty _ _ _ (bound _)
  change (G.toUniformGenerators.layer (2 * (n + 1) + 1)).Nonempty
  rw [G.layer_eq_lengthSlice, language]
  exact h.collision_slice_nonempty n

/-- Both the affine parameter change and the original runtime are bounded by
one polynomial in the attacker's security parameter. -/
theorem collision_generator_reindexed_polynomial (p : PolynomialBound) :
    ∃ q : PolynomialBound, ∀ n, p (2 * (n + 1) + 1) ≤ q n := by
  let size : PolynomialBound := ⟨4, 1, by decide⟩
  refine ⟨p.comp size, fun n => ?_⟩
  apply le_trans ?_ (p.comp_le size n)
  change p.coefficient * (2 * (n + 1) + 1 + 1) ^ p.degree ≤
    p.coefficient * (size n + 1) ^ p.degree
  apply Nat.mul_le_mul_left
  apply pow_le_pow_left'
  simp [size, PolynomialBound.eval]

end ComplexityOfGenerators
