import ComplexityOfGenerators.Proofs.ExpectedOriginalStarSampling.Basic

/-! Star's certified selection can depend on bounded tests, while the fresh
original calls retain their first moments conditional on every selected path. -/
namespace ComplexityOfGenerators.ExpectedOriginalStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

theorem draw_word_mean (mean : G.ExpectedLength) (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    (∫⁻ stream,((outputWord G (((draw G p expected n available).run stream).1)).length : ℝ≥0∞)
      ∂fairCoinMeasure)=(n : ℝ≥0∞) := by
  rw [draw_lintegral G p expected n available (fun result => ((outputWord G result).length : ℝ≥0∞))]
  have each (record : ExpectedStarSampling.OuterRecord p n) :
      (∫⁻ future,((outputWord G (record,
        ((OriginalSourceFamilySampler.calls (families G) (requests G p n (List.ofFn record.2))
          (requests_active G p n (List.ofFn record.2))).run future).1)).length : ℝ≥0∞)∂fairCoinMeasure)=
        ((ExpectedStarSampling.chosenParts G p n (List.ofFn record.2)).sum : ℝ≥0∞) := by
    have initial := OriginalSourceFamilySampler.calls_word_mean (families G) (fun _ => mean)
      (requests G p n (List.ofFn record.2)) (requests_active G p n (List.ofFn record.2))
    simpa [outputWord,requests,Function.comp_def] using initial
  simp_rw [each]
  calc
    _ = ∫⁻ _record,(n : ℝ≥0∞)∂(ExpectedStarSampling.outerCall G p expected n available).distribution := by
      apply lintegral_congr_ae
      filter_upwards [ExpectedStarSampling.outerCall_live G p expected n available] with record accepted
      exact congrArg (fun value : ℕ => (value : ℝ≥0∞))
        (ExpectedStarSampling.chosenParts_spec G p n (List.ofFn record.2) accepted).1.1
    _ = _ := by simp

/-- Only the first moments of the original source runtimes enter this bound.
The selected path contains at most n indices, each at most n. -/
theorem draw_source_runtime_le (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    (∫⁻ stream,(sourceRuntime G (((draw G p expected n available).run stream).1) : ℝ≥0∞)
      ∂fairCoinMeasure)≤(n : ℝ≥0∞)*(p n : ℝ≥0∞) := by
  rw [draw_lintegral G p expected n available (fun result => (sourceRuntime G result : ℝ≥0∞))]
  calc
    _ ≤ ∫⁻ _record,(n : ℝ≥0∞)*(p n : ℝ≥0∞)
        ∂(ExpectedStarSampling.outerCall G p expected n available).distribution := by
      apply lintegral_mono
      intro record
      have bounds := requests_bounds G p n (List.ofFn record.2)
      have initial := OriginalSourceFamilySampler.calls_runtime_le (families G) p (fun _ => expected)
        (requests G p n (List.ofFn record.2)) (requests_active G p n (List.ofFn record.2)) n bounds.2
      exact initial.trans (mul_le_mul' (Nat.cast_le.mpr bounds.1) le_rfl)
    _ = _ := by simp

/-- The bounded outer search retains its geometric second-moment bound;
there is no second-moment assertion about any original source call. -/
theorem draw_outer_secondMoment (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    (∫⁻ stream,(((((draw G p expected n available).run stream).1.1.1+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure)≤8 := by
  rw [draw_lintegral G p expected n available (fun result => ((result.1.1+1 : ℕ) : ℝ≥0∞)^2)]
  simp only [lintegral_const,measure_univ,mul_one]
  have measurable : Measurable (fun stream => ((ExpectedStarSampling.outerCall G p expected n available).run stream).1) :=
    measurable_fst.comp (ExpectedStarSampling.outerCall G p expected n available).measurable
  change (∫⁻ record,((record.1+1 : ℕ) : ℝ≥0∞)^2∂fairCoinMeasure.map
    (fun stream => ((ExpectedStarSampling.outerCall G p expected n available).run stream).1))≤_
  rw [lintegral_map (measurable_of_countable _) measurable]
  exact ExpectedStarSampling.outerCall_secondMoment G p expected n available

end
end ComplexityOfGenerators.ExpectedOriginalStarSampling
