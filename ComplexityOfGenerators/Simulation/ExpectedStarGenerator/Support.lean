import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Native
import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Witnesses
import ComplexityOfGenerators.Foundations.IndexedSupportClosure

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

theorem machine_halting (n : ℕ) : (machine M p P).HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨ticks, result, run, _⟩ := machine_execution M p P n bits
    exact ⟨ticks, result.outcome, run⟩
  · intro bits time rejected
    obtain ⟨ticks, result, run, _⟩ := machine_execution M p P n bits
    have same := (machine M p P).halted_outcome_unique (generatorData n) bits ticks time result.outcome .rejected run rejected
    cases result <;> simp [Result.outcome] at same

private theorem add_positive {parts : List ℕ} {factors : List (List α)}
    (language : List.Forall₂ (fun j word => word ∈ P.layer j) parts factors)
    (positive : ∀ j ∈ parts, 0 < j) : List.Forall₂ (fun j word => 0 < j ∧ word ∈ P.layer j) parts factors := by
  induction language with
  | nil => exact .nil
  | @cons j word parts factors member language ih =>
      exact .cons ⟨positive j (by simp), member⟩ (ih (fun k belongs => positive k (by simp [belongs])))

theorem machine_language_subset (n : ℕ) :
    (machine M p P).generatedLanguage (generatorData n) ⊆ IndexedSupport.starLayers P.layer n := by
  intro word member
  obtain ⟨bits, time, accepted⟩ := ((machine M p P).mem_generatedLanguage_iff_produces _ _).mp member
  obtain ⟨ticks, result, reference, generated⟩ := machine_execution M p P n bits
  have same := (machine M p P).halted_outcome_unique (generatorData n) bits ticks time result.outcome (.accepted word) reference accepted
  cases result with
  | exhausted => simp [Result.outcome] at same
  | done after =>
      obtain ⟨parts, factors, total, positive, language, output⟩ := generated
      have equal : after.output = word := by simpa only [Result.outcome, Outcome.accepted.injEq] using same
      exact ⟨parts, factors, add_positive P language positive, total, output.symm.trans equal⟩

variable (G : UniformGenerators α)
    (layers : ∀ j, P.layer j = G.layer j)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))

def shortClock : PolynomialBound := PolynomialBound.ofPolynomial
  (25*(primitiveCoefficient G.machine p P).asPolynomial^2*(Polynomial.X+2)^2)

theorem shortClock_lower (n : ℕ) :
    25*(primitiveCoefficient G.machine p P n)^2*(n+2)^2 ≤ shortClock p P G n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_pow, PolynomialBound.asPolynomial_eval]
  rfl

include layers expected in
theorem machine_short_path (n : ℕ) (word : List α) (member : word ∈ IndexedSupport.starLayers P.layer n) :
    ∃ bits : BitString, bits ≠ [] ∧ (machine G.machine p P).run (generatorData n) bits (shortClock p P G n) = .halted (.accepted word) := by
  obtain ⟨parts, factors, language, total, flattened⟩ := member
  have active : ∀ j ∈ parts, 0 < j ∧ (G.layer j).Nonempty := by
    clear total flattened
    induction language with
    | nil => simp
    | @cons j factor parts factors head tail ih =>
        intro k belongs
        rcases List.mem_cons.mp belongs with rfl | belongs
        · refine ⟨head.1, factor, ?_⟩
          rw [← layers k]
          exact head.2
        · exact ih k belongs
  have positive : ∀ j ∈ parts, 0 < j := fun j belongs => (active j belongs).1
  have available : CertifiedStarPhase.AvailableComposition G n parts := ⟨total, active⟩
  obtain ⟨outer, outerLength, outerHit⟩ := CertifiedStarPhase.value_full_support G p n parts available expected
  have source : List.Forall₂ (fun j factor => factor ∈ P.layer j) parts factors :=
    List.Forall₂.imp (fun _ _ pair => pair.2) language
  obtain ⟨inner, records, trace, output, number, _⟩ := ExpectedStarCalls.trace_witness P parts factors source
  let bits := outer++inner
  have taken : bits.take (StarCertification.width p n) = outer := by rw [← outerLength]; exact List.take_left
  have shifted : ExpectedStarCalls.Trace P bits (StarCertification.width p n) parts records := by
    simpa only [outerLength, Nat.add_zero] using ExpectedStarCalls.Trace.prepend P trace outer
  obtain ⟨ticks, clock, run⟩ := machine_runs_trace G.machine p P n 0 parts records bits total positive
    (by dsimp [bits]; simp only [List.length_append]; omega) (by intro k less; omega)
    (by simpa only [Nat.zero_mul, List.drop_zero, taken] using outerHit)
    (by simpa only [Nat.zero_add, Nat.one_mul] using shifted)
  have recordsBound : ExpectedStarCalls.blocks records ≤ n := by
    rw [number]
    exact (positive_length_le_sum parts positive).trans_eq total
  have index : 0+1+ExpectedStarCalls.blocks records+1 = ExpectedStarCalls.blocks records+2 := by omega
  rw [index] at clock
  have enlarged := Nat.mul_le_mul_left (25*(primitiveCoefficient G.machine p P n)^2)
    (Nat.pow_le_pow_left (Nat.add_le_add_right recordsBound 2) 2)
  have deadline : ticks ≤ shortClock p P G n := clock.trans (enlarged.trans (shortClock_lower p P G n))
  have nonempty : bits ≠ [] := by
    have width := (StarCertification.width p).positive n
    intro empty
    have lengths := congrArg List.length empty
    simp only [bits, List.length_append, List.length_nil] at lengths
    omega
  have padded := (machine G.machine p P).run_halted_add (generatorData n) bits ticks
    (.accepted (ExpectedStarCalls.words records)) run (shortClock p P G n-ticks)
  refine ⟨bits, nonempty, ?_⟩
  rw [Nat.add_sub_of_le deadline, output, flattened] at padded
  exact padded

include layers expected in
theorem machine_language (n : ℕ) :
    (machine G.machine p P).generatedLanguage (generatorData n) = IndexedSupport.starLayers P.layer n := by
  apply Set.Subset.antisymm (machine_language_subset G.machine p P n)
  intro word member
  obtain ⟨bits, nonempty, run⟩ := machine_short_path p P G layers expected n word member
  exact ⟨bits, nonempty, shortClock p P G n, run⟩

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
