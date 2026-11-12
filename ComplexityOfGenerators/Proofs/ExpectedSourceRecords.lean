import ComplexityOfGenerators.Proofs.ExpectedSourceSampler
import ComplexityOfGenerators.Foundations.CountableLists
import ComplexityOfGenerators.Foundations.FreshStreamTails

/-! Complete source-call records retain the actual word and the exact number
of failed finite blocks. Their probability law comes from the same fresh
retry sampler as the previously established length and cost moments. -/
namespace ComplexityOfGenerators.BoundedPhaseFamily
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

noncomputable def wordRecord (n : ℕ) (active : (P.layer n).Nonempty) :
    FreshStreamSampler (ℕ × List α) :=
  (P.freshCall n active).map
    (fun record => (record.1, ((P.phase n).value record.2).getD [])) (measurable_of_countable _)

theorem wordRecord_mean (n : ℕ) (active : (P.layer n).Nonempty) :
    (∫⁻ stream, ((P.wordRecord n active).run stream).1.2.length ∂fairCoinMeasure) = (n : ℝ≥0∞) :=
  P.callWord_mean n active

theorem wordRecord_secondMoment (n : ℕ) (active : (P.layer n).Nonempty) :
    (∫⁻ stream, ((((P.wordRecord n active).run stream).1.1+1 : ℕ) : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤
      2*(P.reciprocal n : ℝ≥0∞)^2 :=
  P.callAttempts_secondMoment n active

/-- Earlier blocks fail and the selected block produces exactly the recorded
word, outside the null event on which every retry fails. -/
theorem wordRecord_spec_ae (n : ℕ) (active : (P.layer n).Nonempty) :
    ∀ᵐ stream ∂fairCoinMeasure,
      (∀ k < ((P.wordRecord n active).run stream).1.1,
        (P.phase n).value (fixedBlock (P.seed n) stream k) = none) ∧
      (P.phase n).value (fixedBlock (P.seed n) stream ((P.wordRecord n active).run stream).1.1) =
        some ((P.wordRecord n active).run stream).1.2 := by
  filter_upwards [firstSuccessIndex_ae_success (P.seed n) (P.seed.positive n) (P.successSet n)
    (Set.to_countable _ |>.measurableSet) (P.success_positive n active)] with stream success
  have prior (k : ℕ) (earlier : k < firstSuccessIndex (P.seed n) (P.successSet n) stream) :
      (P.phase n).value (fixedBlock (P.seed n) stream k) = none := by
    have absent : fixedBlock (P.seed n) stream k ∉ P.successSet n := by
      rcases firstSuccessIndex_spec (P.seed n) (P.successSet n) stream with ⟨_,first⟩ | ⟨_,never⟩
      · exact first k earlier
      · exact never k
    cases value : (P.phase n).value (fixedBlock (P.seed n) stream k) with
    | none => rfl
    | some word => exact False.elim (absent (by simp [successSet,value]))
  refine ⟨prior,?_⟩
  change (P.phase n).value (selectedBlock (P.seed n) (P.successSet n) stream) =
    some (((P.phase n).value (selectedBlock (P.seed n) (P.successSet n) stream)).getD [])
  change ((P.phase n).value (selectedBlock (P.seed n) (P.successSet n) stream)).isSome = true at success
  cases value : (P.phase n).value (selectedBlock (P.seed n) (P.successSet n) stream) with
  | none => simp only [value,Option.isSome_none,Bool.false_eq_true] at success
  | some word => simp [value]

theorem wordRecord_tail (n : ℕ) (active : (P.layer n).Nonempty) (stream : BitStream) :
    ((P.wordRecord n active).run stream).2 =
      fun i => stream ((((P.wordRecord n active).run stream).1.1+1)*P.seed n+i) := rfl

end
end ComplexityOfGenerators.BoundedPhaseFamily
