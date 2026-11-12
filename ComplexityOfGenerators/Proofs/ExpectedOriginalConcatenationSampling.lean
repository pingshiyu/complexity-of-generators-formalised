import ComplexityOfGenerators.Proofs.OriginalCertification.Concatenation
import ComplexityOfGenerators.Proofs.SelectedOriginalSampling.Moments
import ComplexityOfGenerators.Proofs.SelectedOriginalSampling.Trace

namespace ComplexityOfGenerators.ExpectedOriginalConcatenationSampling
open MeasureTheory
open scoped ENNReal
open OriginalSourceFamilySampler (Request)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

def selection (n : ℕ) (bits : BitString) : Option (List Request) :=
  (OriginalCertification.Concatenation.choice families p n bits).map (fun j => [(false,j),(true,n-j)])

include expected in
theorem selection_sound (n : ℕ) (bits : BitString) (requests : List Request)
    (result : selection families p n bits=some requests) :
    ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty := by
  obtain ⟨j,chosen,equal⟩ := Option.map_eq_some_iff.mp result
  subst requests
  have active := OriginalCertification.Concatenation.choice_sound families p expected n bits chosen
  intro entry member
  rcases List.mem_cons.mp member with same|member
  · simpa only [same] using active.2.1
  · have same := List.mem_singleton.mp member
    simpa only [same] using active.2.2

include expected in
theorem selection_balanced (n : ℕ) (bits : BitString) (requests : List Request)
    (result : selection families p n bits=some requests) : (requests.map Prod.snd).sum=n := by
  obtain ⟨j,chosen,equal⟩ := Option.map_eq_some_iff.mp result
  subst requests
  have within := (OriginalCertification.Concatenation.choice_sound families p expected n bits chosen).1
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

include expected in
theorem selection_bounds (n : ℕ) (bits : BitString) (requests : List Request)
    (result : selection families p n bits=some requests) : requests.length≤2 ∧ ∀ entry∈requests,entry.2≤n := by
  obtain ⟨j,chosen,equal⟩ := Option.map_eq_some_iff.mp result
  subst requests
  have within := (OriginalCertification.Concatenation.choice_sound families p expected n bits chosen).1
  refine ⟨le_rfl,?_⟩
  intro entry member
  rcases List.mem_cons.mp member with same|member
  · simpa only [same] using within
  · have same := List.mem_singleton.mp member
    simpa only [same] using Nat.sub_le n j

include expected in
theorem mass (n : ℕ) (available : OriginalCertification.Concatenation.Available families n) :
    (1 : ℝ≥0∞)/4≤fairBlockMeasure (OriginalCertification.Concatenation.width p n)
      (SelectedOriginalSampling.success (OriginalCertification.Concatenation.width p) (selection families p) n) := by
  simpa only [SelectedOriginalSampling.success,selection,Option.isSome_map] using
    OriginalCertification.Concatenation.choice_mass families p expected n available

include expected in
theorem positive (n : ℕ) (available : OriginalCertification.Concatenation.Available families n) :
    0<fairBlockMeasure (OriginalCertification.Concatenation.width p n)
      (SelectedOriginalSampling.success (OriginalCertification.Concatenation.width p) (selection families p) n) :=
  (by norm_num : (0 : ℝ≥0∞)<1/4).trans_le (mass families p expected n available)

def draw (n : ℕ) (available : OriginalCertification.Concatenation.Available families n) :=
  SelectedOriginalSampling.draw families (OriginalCertification.Concatenation.width p) (selection families p)
    (selection_sound families p expected) n (positive families p expected n available)

theorem draw_word_mean (mean : ∀ tag,(families tag).ExpectedLength)
    (n : ℕ) (available : OriginalCertification.Concatenation.Available families n) :
    (∫⁻ stream,((SelectedOriginalSampling.outputWord families (OriginalCertification.Concatenation.width p)
      (((draw families p expected n available).run stream).1)).length : ℝ≥0∞)∂fairCoinMeasure)=(n : ℝ≥0∞) :=
  SelectedOriginalSampling.draw_word_mean families (OriginalCertification.Concatenation.width p) (selection families p)
    (selection_sound families p expected) mean n (positive families p expected n available)
      (selection_balanced families p expected n)

theorem draw_source_runtime_le (n : ℕ) (available : OriginalCertification.Concatenation.Available families n) :
    (∫⁻ stream,(SelectedOriginalSampling.sourceRuntime families (OriginalCertification.Concatenation.width p)
      (((draw families p expected n available).run stream).1) : ℝ≥0∞)∂fairCoinMeasure)≤2*(p n : ℝ≥0∞) := by
  have initial := SelectedOriginalSampling.draw_source_runtime_le families (OriginalCertification.Concatenation.width p)
    (selection families p) (selection_sound families p expected) p expected n
      (positive families p expected n available) 2 (selection_bounds families p expected n)
  simpa only [draw,Nat.cast_ofNat] using initial

theorem draw_outer_secondMoment (n : ℕ) (available : OriginalCertification.Concatenation.Available families n) :
    (∫⁻ stream,(((((draw families p expected n available).run stream).1.1.1+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure)≤32 := by
  have initial := SelectedOriginalSampling.draw_outer_secondMoment families (OriginalCertification.Concatenation.width p)
    (selection families p) (selection_sound families p expected) n
      (positive families p expected n available) 4 (by
        simpa only [Nat.cast_ofNat,one_div] using mass families p expected n available)
  norm_num at initial ⊢
  exact initial

end
end ComplexityOfGenerators.ExpectedOriginalConcatenationSampling
