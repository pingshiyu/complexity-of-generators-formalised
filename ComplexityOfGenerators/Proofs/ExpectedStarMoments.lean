import ComplexityOfGenerators.Proofs.ExpectedStarRecords
import ComplexityOfGenerators.Foundations.SequentialCostMoments

/-! The full word records used by the native trace have the required length
mean and retry-count second moment. No extra source variance bound is needed. -/
namespace ComplexityOfGenerators.BoundedPhaseFamily
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

@[simp] theorem nativeRecords_words (records : List (ℕ × List α)) :
    ExpectedStarCalls.words (nativeRecords records) = records.flatMap Prod.snd := by
  simp [nativeRecords,ExpectedStarCalls.words,List.flatMap_map]

@[simp] theorem nativeRecords_blocks (records : List (ℕ × List α)) :
    ExpectedStarCalls.blocks (nativeRecords records) = (records.map (fun record => record.1+1)).sum := by
  simp [nativeRecords,ExpectedStarCalls.blocks,ExpectedStarCalls.Record.blocks,List.map_map,Function.comp_def]

noncomputable def factorCalls (parts : List ℕ) (active : ∀ j ∈ parts, (P.layer j).Nonempty) :
    FreshStreamSampler (ℕ × ℕ) :=
  (P.recordCalls parts active).map
    (fun records => ((ExpectedStarCalls.words (nativeRecords records)).length,
      ExpectedStarCalls.blocks (nativeRecords records))) (measurable_of_countable _)

/-- Fresh full-word records give the specified total expected length for any
fixed composition of productive source indices. -/
theorem factorCalls_mean (parts : List ℕ) (active : ∀ j ∈ parts, (P.layer j).Nonempty) :
    (∫⁻ stream, ((P.factorCalls parts active).run stream).1.1 ∂fairCoinMeasure) =
      (parts.sum : ℝ≥0∞) := by
  change (∫⁻ stream, ((ExpectedStarCalls.words (nativeRecords
    (List.ofFn ((FreshStreamSampler.sequence (P.recordSamplers parts active)).run stream).1))).length : ℝ≥0∞)
      ∂fairCoinMeasure) = _
  simp only [nativeRecords_words,List.length_flatMap,List.map_ofFn,List.sum_ofFn,Nat.cast_sum]
  have means := FreshStreamSampler.sequence_lintegral_sum (P.recordSamplers parts active)
    (fun result : ℕ × List α => (result.2.length : ℝ≥0∞))
  refine means.trans ?_
  unfold recordSamplers
  rw [List.map_map]
  change (parts.attach.map (fun part => ∫⁻ stream,
    ((P.wordRecord part.1 (active part.1 part.2)).run stream).1.2.length ∂fairCoinMeasure)).sum = _
  simp_rw [P.wordRecord_mean]
  simp

/-- The number of calls pays for all cross terms in the squared total retry
cost, including correlation with the generated word lengths. -/
theorem factorCalls_secondMoment (parts : List ℕ) (active : ∀ j ∈ parts, (P.layer j).Nonempty)
    (target : ℕ) (indices : ∀ j ∈ parts, j ≤ target) (count : parts.length ≤ target) :
    (∫⁻ stream, (((P.factorCalls parts active).run stream).1.2 : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤
      2*(target : ℝ≥0∞)^2*(P.reciprocal target : ℝ≥0∞)^2 := by
  have each : ∀ sampler ∈ P.recordSamplers parts active,
      (∫⁻ stream, (((sampler.run stream).1.1+1 : ℕ) : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤
        2*(P.reciprocal target : ℝ≥0∞)^2 := by
    intro sampler member
    obtain ⟨part,_,rfl⟩ := List.mem_map.mp member
    have initial := P.wordRecord_secondMoment part.1 (active part.1 part.2)
    have monotone : (P.reciprocal part.1 : ℝ≥0∞) ≤ (P.reciprocal target : ℝ≥0∞) := by
      have ordered : P.reciprocal part.1 ≤ P.reciprocal target :=
        Nat.mul_le_mul_left P.reciprocal.coefficient
          (pow_le_pow_left' (by have := indices part.1 part.2; omega) P.reciprocal.degree)
      exact_mod_cast ordered
    exact initial.trans (mul_le_mul' le_rfl (pow_le_pow_left' monotone 2))
  have bound := FreshStreamSampler.sequence_totalCost_secondMoment
    (P.recordSamplers parts active) (fun record => record.1+1) (2*(P.reciprocal target : ℝ≥0∞)^2) each
  have length : (P.recordSamplers parts active).length = parts.length := by simp [recordSamplers]
  change (∫⁻ stream, ((ExpectedStarCalls.blocks (nativeRecords
    (List.ofFn ((FreshStreamSampler.sequence (P.recordSamplers parts active)).run stream).1)) : ℝ≥0∞)^2)
      ∂fairCoinMeasure) ≤ _
  simp only [nativeRecords_blocks,List.map_ofFn,List.sum_ofFn]
  apply bound.trans
  rw [length]
  have casted : (parts.length : ℝ≥0∞) ≤ (target : ℝ≥0∞) := by exact_mod_cast count
  calc
    _ ≤ (target : ℝ≥0∞)^2*(2*(P.reciprocal target : ℝ≥0∞)^2) :=
      mul_le_mul' (pow_le_pow_left' casted 2) le_rfl
    _ = _ := by ring

end
end ComplexityOfGenerators.BoundedPhaseFamily
