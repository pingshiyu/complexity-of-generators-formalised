import ComplexityOfGenerators.Proofs.BoundedPhaseFamilies
import ComplexityOfGenerators.Foundations.FreshStreamSamplers
import ComplexityOfGenerators.Simulation.FixedBlockRetry.LoopSuccess

/-! A normalised source call as an actual fresh-stream sampler. Its output
mean and attempted-block second moment follow from the source's first moments;
the source need not satisfy any extra tail or variance assumption. -/
namespace ComplexityOfGenerators.BoundedPhaseFamily
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

def successSet (n : ℕ) : Set (Fin (P.seed n) → Bool) := {bits | ((P.phase n).value bits).isSome}

theorem success_positive (n : ℕ) (active : (P.layer n).Nonempty) :
    0 < fairBlockMeasure (P.seed n) (P.successSet n) := by
  obtain ⟨word, member⟩ := active
  obtain ⟨bits, output⟩ := (P.layer_iff n word).mp member
  have lower := P.mass n ⟨bits, word, output⟩
  exact lt_of_lt_of_le (by simp) lower

noncomputable def freshCall (n : ℕ) (active : (P.layer n).Nonempty) :
    FreshStreamSampler (ℕ × (Fin (P.seed n) → Bool)) :=
  FreshStreamSampler.retry (P.seed n) (P.seed.positive n) (P.successSet n)
    (Set.to_countable _ |>.measurableSet) (P.success_positive n active)

def callWord (n : ℕ) (stream : BitStream) : List α :=
  ((P.phase n).value (selectedBlock (P.seed n) (P.successSet n) stream)).getD []

def callAttempts (n : ℕ) (stream : BitStream) : ℕ :=
  firstSuccessIndex (P.seed n) (P.successSet n) stream + 1

/-- Full output support is retained; unsuccessful infinite streams form a
null set on every productive source index. -/
theorem callWord_mem_ae (n : ℕ) (active : (P.layer n).Nonempty) :
    ∀ᵐ stream ∂fairCoinMeasure, P.callWord n stream ∈ P.layer n := by
  filter_upwards [firstSuccessIndex_ae_success (P.seed n) (P.seed.positive n) (P.successSet n)
    (Set.to_countable _ |>.measurableSet) (P.success_positive n active)] with stream accepted
  let bits := selectedBlock (P.seed n) (P.successSet n) stream
  have produced : ((P.phase n).value bits).isSome := accepted
  cases output : (P.phase n).value bits with
  | none => simp only [output, Option.isSome_none, Bool.false_eq_true] at produced
  | some word =>
    rw [P.layer_iff]
    refine ⟨bits, ?_⟩
    change (P.phase n).value bits = some (P.callWord n stream)
    change (P.phase n).value bits = some (((P.phase n).value bits).getD [])
    rw [output]
    rfl

/-- A fresh retry call has the original target mean exactly. -/
theorem callWord_mean (n : ℕ) (active : (P.layer n).Nonempty) :
    (∫⁻ stream, (P.callWord n stream).length ∂fairCoinMeasure) = (n : ℝ≥0∞) := by
  let value := fun bits : Fin (P.seed n) → Bool => (((P.phase n).value bits).getD []).length
  have lengthEqual (bits : Fin (P.seed n) → Bool) :
      (value bits : ℝ≥0∞) = (BalancedPairPhase.optionLength ((P.phase n).value bits) : ℝ≥0∞) := by
    dsimp only [value]
    cases (P.phase n).value bits <;> rfl
  have mean : (∫⁻ bits, (value bits : ℝ≥0∞) ∂fairBlockMeasure (P.seed n)) =
      (n : ℝ≥0∞) * fairBlockMeasure (P.seed n) (P.successSet n) := by
    simp_rw [lengthEqual]
    exact P.mean n
  have zero (bits : Fin (P.seed n) → Bool) (absent : bits ∉ P.successSet n) : (value bits : ℝ≥0∞) = 0 := by
    cases failed : (P.phase n).value bits with
    | none => simp only [value, failed, Option.getD_none, List.length_nil, Nat.cast_zero]
    | some word => exact False.elim (absent (by change ((P.phase n).value bits).isSome = true; simp [failed]))
  exact lintegral_selectedBlock_eq_of_phase_mean (P.seed n) (P.seed.positive n) (P.successSet n)
    (Set.to_countable _ |>.measurableSet) (P.success_positive n active) (fun bits => value bits)
    (measurable_of_countable _) zero (n : ℝ≥0∞) mean

/-- Only the normalised bounded phase is retried. Its second moment is a
proved consequence of inverse-polynomial success, not a source hypothesis. -/
theorem callAttempts_secondMoment (n : ℕ) (active : (P.layer n).Nonempty) :
    (∫⁻ stream, (P.callAttempts n stream : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤
      2 * (P.reciprocal n : ℝ≥0∞)^2 := by
  obtain ⟨word, member⟩ := active
  obtain ⟨bits, output⟩ := (P.layer_iff n word).mp member
  have lower := P.mass n ⟨bits, word, output⟩
  change (P.reciprocal n : ℝ≥0∞)⁻¹ ≤ fairBlockMeasure (P.seed n) (P.successSet n) at lower
  have inverse : (fairBlockMeasure (P.seed n) (P.successSet n))⁻¹ ≤ (P.reciprocal n : ℝ≥0∞) := by
    simpa only [inv_inv] using ENNReal.inv_le_inv.mpr lower
  have moment := firstSuccessIndex_secondMoment_le (P.seed n) (P.seed.positive n) (P.successSet n)
    (Set.to_countable _ |>.measurableSet)
  change (∫⁻ stream, (P.callAttempts n stream : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤ _ at moment
  apply moment.trans
  rw [div_eq_mul_inv, ENNReal.inv_pow]
  gcongr

/-- Length and attempted-block count together retain the same fresh suffix.
Recording both explicitly permits arbitrary correlation within one call. -/
noncomputable def lengthAttempts (n : ℕ) (active : (P.layer n).Nonempty) : FreshStreamSampler (ℕ × ℕ) :=
  (P.freshCall n active).map
    (fun record => ((((P.phase n).value record.2).getD []).length, record.1+1))
    (measurable_of_countable _)

theorem lengthAttempts_mean (n : ℕ) (active : (P.layer n).Nonempty) :
    (∫⁻ stream, ((P.lengthAttempts n active).run stream).1.1 ∂fairCoinMeasure) = (n : ℝ≥0∞) := by
  exact P.callWord_mean n active

theorem lengthAttempts_secondMoment (n : ℕ) (active : (P.layer n).Nonempty) :
    (∫⁻ stream, (((P.lengthAttempts n active).run stream).1.2 : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤
      2*(P.reciprocal n : ℝ≥0∞)^2 := by
  exact P.callAttempts_secondMoment n active

end
end ComplexityOfGenerators.BoundedPhaseFamily
