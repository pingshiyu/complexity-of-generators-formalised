import ComplexityOfGenerators.MultitapeComplexityClasses
import ComplexityOfGenerators.Simulation.TransducerBank.Native.Semantics
import ComplexityOfGenerators.Foundations.ResourceBounds

/-!
# Polynomial compatibility of native and genuine multitape time

The native-to-bank direction is transition preserving. The reverse direction
uses the actual quadratic bank compiler and accounts for its full cost. Thus
this equivalence does not assert preservation of an arbitrary time bound.
-/

namespace ComplexityOfGenerators.Multitape

noncomputable section

variable (α : Type) [Fintype α]

def NP : LanguageClass α :=
  {language | ∃ M : MultitapeMachine α Bool Unit, ∃ time : PolynomialBound,
    (∀ word, M.TimeBound (decisionData word) (time word.length)) ∧
    ∀ word, (∃ bits, M.Accepts (decisionData word) bits) ↔ word ∈ language}

def compiledPolynomialTime (time : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (1 + (time.asPolynomial + 1) * (2 * time.asPolynomial + 4))

theorem compiledPolynomialTime_bound (time : PolynomialBound) (n : ℕ) :
    1 + (time n + 1) * (2 * time n + 4) ≤ compiledPolynomialTime time n := by
  unfold compiledPolynomialTime
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_ofNat, PolynomialBound.asPolynomial_eval] using
    PolynomialBound.eval_le_ofPolynomial
      (1 + (time.asPolynomial + 1) * (2 * time.asPolynomial + 4)) n

/-- A checked polynomial equivalence, with both finite machine implementations. -/
theorem np_eq_native_np : NP α = ComplexityOfGenerators.NP α := by
  ext language
  constructor
  · rintro ⟨M, time, bounded, recognizes⟩
    refine ⟨M.toNative, compiledPolynomialTime time, ?_, ?_⟩
    · intro word bits
      obtain ⟨result, run⟩ :=
        M.timeBound_toNative (decisionData word) (time word.length) (bounded word) bits
      have cost := compiledPolynomialTime_bound time word.length
      refine ⟨result, ?_⟩
      have later := M.toNative.run_halted_add (decisionData word) bits
        (1 + (time word.length + 1) * (2 * time word.length + 4)) result run
        (compiledPolynomialTime time word.length -
          (1 + (time word.length + 1) * (2 * time word.length + 4)))
      simpa only [Nat.add_sub_of_le cost] using later
    · intro word
      have terminates : M.Terminates (decisionData word) := by
        intro bits
        obtain ⟨ticks, result, _, execution⟩ := bounded word bits
        exact ⟨ticks, result, execution⟩
      rw [show (∃ bits, M.toNative.Accepts (decisionData word) bits) ↔
          (∃ bits, M.Accepts (decisionData word) bits) from
        exists_congr fun bits => M.accepts_toNative_iff (decisionData word) terminates bits]
      exact recognizes word
  · rintro ⟨M, time, bounded, recognizes⟩
    refine ⟨Simulation.TransducerBank.Native.machine M, time,
      fun word => Simulation.TransducerBank.Native.timeBound M _ _ (bounded word), ?_⟩
    intro word
    have halts : ∀ bits, M.Halts (decisionData word) bits :=
      fun bits => ⟨time word.length, bounded word bits⟩
    rw [show (∃ bits, (Simulation.TransducerBank.Native.machine M).Accepts
        (decisionData word) bits) ↔ (∃ bits, M.Accepts (decisionData word) bits) from
      exists_congr fun bits => Simulation.TransducerBank.Native.accepts_iff M
        (decisionData word) halts bits]
    exact recognizes word

end
end ComplexityOfGenerators.Multitape
