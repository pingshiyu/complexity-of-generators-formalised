import ComplexityOfGenerators.Proofs.OriginalCertification.Union
import ComplexityOfGenerators.Proofs.SelectedOriginalSampling.Moments
import ComplexityOfGenerators.Proofs.SelectedOriginalSampling.Trace

namespace ComplexityOfGenerators.ExpectedOriginalUnionSampling
open MeasureTheory
open scoped ENNReal
open OriginalSourceFamilySampler (Request)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

def selection (n : ℕ) (bits : BitString) : Option (List Request) :=
  (OriginalCertification.Union.choice families p n bits).map (fun tag => [(tag,n)])

include expected in
theorem selection_sound (n : ℕ) (bits : BitString) (requests : List Request)
    (result : selection families p n bits=some requests) :
    ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty := by
  obtain ⟨tag,chosen,equal⟩ := Option.map_eq_some_iff.mp result
  subst requests
  intro entry member
  have same : entry=(tag,n) := List.mem_singleton.mp member
  subst entry
  exact OriginalCertification.Union.choice_sound families p expected n bits chosen

theorem selection_balanced (n : ℕ) (bits : BitString) (requests : List Request)
    (result : selection families p n bits=some requests) : (requests.map Prod.snd).sum=n := by
  obtain ⟨tag,_,equal⟩ := Option.map_eq_some_iff.mp result
  subst requests
  simp

theorem selection_bounds (n : ℕ) (bits : BitString) (requests : List Request)
    (result : selection families p n bits=some requests) : requests.length≤1 ∧ ∀ entry∈requests,entry.2≤n := by
  obtain ⟨tag,_,equal⟩ := Option.map_eq_some_iff.mp result
  subst requests
  simp

include expected in
theorem mass (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :
    (1 : ℝ≥0∞)/2≤fairBlockMeasure (OriginalCertification.Union.width p n)
      (SelectedOriginalSampling.success (OriginalCertification.Union.width p) (selection families p) n) := by
  simpa only [SelectedOriginalSampling.success,selection,Option.isSome_map] using
    OriginalCertification.Union.choice_mass families p expected n available

include expected in
theorem positive (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :
    0<fairBlockMeasure (OriginalCertification.Union.width p n)
      (SelectedOriginalSampling.success (OriginalCertification.Union.width p) (selection families p) n) :=
  (by norm_num : (0 : ℝ≥0∞)<1/2).trans_le (mass families p expected n available)

def draw (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :=
  SelectedOriginalSampling.draw families (OriginalCertification.Union.width p) (selection families p)
    (selection_sound families p expected) n (positive families p expected n available)

theorem draw_word_mean (mean : ∀ tag,(families tag).ExpectedLength)
    (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :
    (∫⁻ stream,((SelectedOriginalSampling.outputWord families (OriginalCertification.Union.width p)
      (((draw families p expected n available).run stream).1)).length : ℝ≥0∞)∂fairCoinMeasure)=(n : ℝ≥0∞) :=
  SelectedOriginalSampling.draw_word_mean families (OriginalCertification.Union.width p) (selection families p)
    (selection_sound families p expected) mean n (positive families p expected n available)
      (selection_balanced families p n)

theorem draw_source_runtime_le (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :
    (∫⁻ stream,(SelectedOriginalSampling.sourceRuntime families (OriginalCertification.Union.width p)
      (((draw families p expected n available).run stream).1) : ℝ≥0∞)∂fairCoinMeasure)≤(p n : ℝ≥0∞) := by
  have initial := SelectedOriginalSampling.draw_source_runtime_le families (OriginalCertification.Union.width p)
    (selection families p) (selection_sound families p expected) p expected n
      (positive families p expected n available) 1 (selection_bounds families p n)
  simpa only [draw,Nat.cast_one,one_mul] using initial

theorem draw_outer_secondMoment (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :
    (∫⁻ stream,(((((draw families p expected n available).run stream).1.1.1+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure)≤8 := by
  have initial := SelectedOriginalSampling.draw_outer_secondMoment families (OriginalCertification.Union.width p)
    (selection families p) (selection_sound families p expected) n
      (positive families p expected n available) 2 (by
        simpa only [Nat.cast_ofNat,one_div] using mass families p expected n available)
  norm_num at initial ⊢
  exact initial

end
end ComplexityOfGenerators.ExpectedOriginalUnionSampling
