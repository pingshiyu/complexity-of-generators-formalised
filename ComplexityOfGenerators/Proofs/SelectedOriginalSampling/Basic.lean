import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler

/-! Retry a concrete finite certificate phase, then make fresh original
source calls at its certified requests. This is stream probability calculus;
native implementations of the concrete certificate phases are separate. -/
namespace ComplexityOfGenerators.SelectedOriginalSampling
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OriginalSourceFamilySampler (Request Record)
variable {α : Type} (families : Bool → UniformGenerators α) (width : PolynomialBound)
    (value : ℕ → BitString → Option (List Request))

def success (n : ℕ) : Set (Fin (width n) → Bool) := {bits | (value n (List.ofFn bits)).isSome}
abbrev OuterRecord (width : PolynomialBound) (n : ℕ) := ℕ × (Fin (width n) → Bool)
abbrev DrawResult (width : PolynomialBound) (n : ℕ) := OuterRecord width n × List Record
def selected (n : ℕ) (record : OuterRecord width n) : List Request := (value n (List.ofFn record.2)).getD []

def outer (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) :
    FreshStreamSampler (OuterRecord width n) :=
  FreshStreamSampler.retry (width n) (width.positive n) (success width value n)
    (Set.to_countable _ |>.measurableSet) positive

variable (sound : ∀ n bits requests,value n bits=some requests →
  ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty)

include sound in
theorem selected_active (n : ℕ) (record : OuterRecord width n) :
    ∀ entry∈selected width value n record,((families entry.1).layer entry.2).Nonempty := by
  cases found : value n (List.ofFn record.2) with
  | none => simp [selected,found]
  | some requests => simpa only [selected,found,Option.getD_some] using sound n (List.ofFn record.2) requests found

def draw (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) :
    FreshStreamSampler (DrawResult width n) :=
  (outer width value n positive).bind (fun record =>
    (OriginalSourceFamilySampler.calls families (selected width value n record)
      (selected_active families width value sound n record)).map (fun records => (record,records))
        (measurable_of_countable _))

def outputWord {n : ℕ} (result : DrawResult width n) : List α := OriginalSourceFamilySampler.words families result.2
def sourceRuntime {n : ℕ} (result : DrawResult width n) : ℕ := OriginalSourceFamilySampler.totalTime families result.2
def sourceCoins {n : ℕ} (result : DrawResult width n) : ℕ := OriginalSourceFamilySampler.consumed result.2
def outerOffset {n : ℕ} (result : DrawResult width n) : ℕ := (result.1.1+1)*width n

theorem outer_success_ae (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) :
    ∀ᵐ stream∂fairCoinMeasure,(value n (List.ofFn ((outer width value n positive).run stream).1.2)).isSome=true :=
  firstSuccessIndex_ae_success (width n) (width.positive n) (success width value n)
    (Set.to_countable _ |>.measurableSet) positive

theorem outer_live (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) :
    ∀ᵐ record∂(outer width value n positive).distribution,(value n (List.ofFn record.2)).isSome=true := by
  exact ((outer width value n positive).distribution_ae_iff _ (Set.to_countable _ |>.measurableSet)).mpr
    (outer_success_ae width value n positive)

theorem draw_lintegral (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n))
    (cost : DrawResult width n → ℝ≥0∞) :
    (∫⁻ stream,cost (((draw families width value sound n positive).run stream).1)∂fairCoinMeasure)=
      ∫⁻ record, ∫⁻ future,cost (record,
        ((OriginalSourceFamilySampler.calls families (selected width value n record)
          (selected_active families width value sound n record)).run future).1)∂fairCoinMeasure
            ∂(outer width value n positive).distribution := by
  exact FreshStreamSampler.lintegral_bind (outer width value n positive)
    (fun record => (OriginalSourceFamilySampler.calls families (selected width value n record)
      (selected_active families width value sound n record)).map (fun records => (record,records))
        (measurable_of_countable _)) cost (measurable_of_countable _)

end
end ComplexityOfGenerators.SelectedOriginalSampling
