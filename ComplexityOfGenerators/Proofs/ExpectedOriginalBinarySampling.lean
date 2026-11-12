import ComplexityOfGenerators.Proofs.ExpectedOriginalUnionSampling
import ComplexityOfGenerators.Proofs.ExpectedOriginalConcatenationSampling
import ComplexityOfGenerators.Simulation.OriginalBinarySelector.Operation

/-! The two binary closures share one original-source sampler interface.
Only the bounded certificate selector differs; source moments stay first order. -/
namespace ComplexityOfGenerators.ExpectedOriginalBinarySampling
open MeasureTheory
open scoped ENNReal
open Simulation.OriginalBinarySelector (Operation)
open OriginalSourceFamilySampler (Request)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool→UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

def width : Operation→PolynomialBound
  | .union => OriginalCertification.Union.width p
  | .concatenation => OriginalCertification.Concatenation.width p

def selection (operation : Operation) : ℕ→BitString→Option (List Request) :=
  match operation with
  | .union => ExpectedOriginalUnionSampling.selection families p
  | .concatenation => ExpectedOriginalConcatenationSampling.selection families p

def Available : Operation→ℕ→Prop
  | .union,n => ∃ tag,((families tag).layer n).Nonempty
  | .concatenation,n => OriginalCertification.Concatenation.Available families n

include expected in
theorem selection_sound (operation : Operation) (n : ℕ) (bits : BitString) (requests : List Request)
    (accepted : selection families p operation n bits=some requests) :
    ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty := by
  cases operation with
  | union => exact ExpectedOriginalUnionSampling.selection_sound families p expected n bits requests accepted
  | concatenation => exact ExpectedOriginalConcatenationSampling.selection_sound families p expected n bits requests accepted

include expected in
theorem selection_balanced (operation : Operation) (n : ℕ) (bits : BitString) (requests : List Request)
    (accepted : selection families p operation n bits=some requests) : (requests.map Prod.snd).sum=n := by
  cases operation with
  | union => exact ExpectedOriginalUnionSampling.selection_balanced families p n bits requests accepted
  | concatenation => exact ExpectedOriginalConcatenationSampling.selection_balanced families p expected n bits requests accepted

include expected in
theorem selection_bounds (operation : Operation) (n : ℕ) (bits : BitString) (requests : List Request)
    (accepted : selection families p operation n bits=some requests) :
    requests.length≤2 ∧ ∀ entry∈requests,entry.2≤n := by
  cases operation with
  | union =>
      have bound := ExpectedOriginalUnionSampling.selection_bounds families p n bits requests accepted
      exact ⟨bound.1.trans (by omega),bound.2⟩
  | concatenation => exact ExpectedOriginalConcatenationSampling.selection_bounds families p expected n bits requests accepted

include expected in
theorem mass (operation : Operation) (n : ℕ) (available : Available families operation n) :
    (1 : ℝ≥0∞)/4≤fairBlockMeasure (width p operation n)
      (SelectedOriginalSampling.success (width p operation) (selection families p operation) n) := by
  cases operation with
  | union =>
      have bound := ExpectedOriginalUnionSampling.mass families p expected n available
      exact (by norm_num : (1 : ℝ≥0∞)/4≤1/2).trans bound
  | concatenation => exact ExpectedOriginalConcatenationSampling.mass families p expected n available

include expected in
theorem positive (operation : Operation) (n : ℕ) (available : Available families operation n) :
    0<fairBlockMeasure (width p operation n)
      (SelectedOriginalSampling.success (width p operation) (selection families p operation) n) :=
  (by norm_num : (0 : ℝ≥0∞)<1/4).trans_le (mass families p expected operation n available)

include expected in
def draw (operation : Operation) (n : ℕ) (available : Available families operation n) :=
  SelectedOriginalSampling.draw families (width p operation) (selection families p operation)
    (selection_sound families p expected operation) n (positive families p expected operation n available)

include expected in
theorem draw_word_mean (mean : ∀ tag,(families tag).ExpectedLength)
    (operation : Operation) (n : ℕ) (available : Available families operation n) :
    (∫⁻ stream,((SelectedOriginalSampling.outputWord families (width p operation)
      (((draw families p expected operation n available).run stream).1)).length : ℝ≥0∞)∂fairCoinMeasure)=(n : ℝ≥0∞) :=
  SelectedOriginalSampling.draw_word_mean families (width p operation) (selection families p operation)
    (selection_sound families p expected operation) mean n (positive families p expected operation n available)
      (selection_balanced families p expected operation n)

include expected in
theorem draw_source_runtime_le (operation : Operation) (n : ℕ) (available : Available families operation n) :
    (∫⁻ stream,(SelectedOriginalSampling.sourceRuntime families (width p operation)
      (((draw families p expected operation n available).run stream).1) : ℝ≥0∞)∂fairCoinMeasure)≤2*(p n : ℝ≥0∞) := by
  have initial := SelectedOriginalSampling.draw_source_runtime_le families (width p operation)
    (selection families p operation) (selection_sound families p expected operation) p expected n
      (positive families p expected operation n available) 2 (selection_bounds families p expected operation n)
  simpa only [draw,Nat.cast_ofNat] using initial

include expected in
theorem draw_outer_secondMoment (operation : Operation) (n : ℕ) (available : Available families operation n) :
    (∫⁻ stream,(((((draw families p expected operation n available).run stream).1.1.1+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure)≤32 := by
  have initial := SelectedOriginalSampling.draw_outer_secondMoment families (width p operation)
    (selection families p operation) (selection_sound families p expected operation) n
      (positive families p expected operation n available) 4 (by
        simpa only [Nat.cast_ofNat,one_div] using mass families p expected operation n available)
  norm_num at initial ⊢
  exact initial

include expected in
theorem draw_trace_ae (operation : Operation) (n : ℕ) (available : Available families operation n) :
    ∀ᵐ stream∂fairCoinMeasure,
      let sample := ((draw families p expected operation n available).run stream).1
      (∀ k<sample.1.1,selection families p operation n (List.ofFn (fixedBlock (width p operation n) stream k))=none) ∧
      selection families p operation n (List.ofFn (fixedBlock (width p operation n) stream sample.1.1))=
        some (SelectedOriginalSampling.selected (width p operation) (selection families p operation) n sample.1) ∧
      OriginalSourceFamilySampler.StreamTrace families
        (fun i=>stream (SelectedOriginalSampling.outerOffset (width p operation) sample+i))
        (SelectedOriginalSampling.selected (width p operation) (selection families p operation) n sample.1) sample.2 :=
  SelectedOriginalSampling.draw_trace_ae families (width p operation) (selection families p operation)
    (selection_sound families p expected operation) n (positive families p expected operation n available)

end
end ComplexityOfGenerators.ExpectedOriginalBinarySampling
