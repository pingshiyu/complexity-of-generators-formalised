import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler.Moments
import ComplexityOfGenerators.Proofs.ExpectedStarSampleMoments

/-! Certified path selection is followed by fresh calls to the ORIGINAL
sources. Their outputs are not capped, reweighted or normalised. -/
namespace ComplexityOfGenerators.ExpectedOriginalStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

def families (G : UniformGenerators α) : Bool → UniformGenerators α := fun _ => G

def requests (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    List OriginalSourceFamilySampler.Request :=
  (ExpectedStarSampling.chosenParts G p n bits).map (fun j => (false,j))

theorem requests_active (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    ∀ entry∈requests G p n bits,((families G entry.1).layer entry.2).Nonempty := by
  intro entry member
  change entry∈(ExpectedStarSampling.chosenParts G p n bits).map (fun j => (false,j)) at member
  obtain ⟨index,inParts,equal⟩ :=
    (List.mem_map (f := fun j : ℕ => (false,j)) (l := ExpectedStarSampling.chosenParts G p n bits)).mp member
  subst entry
  exact ExpectedStarSampling.chosenParts_active G p n bits index inParts

theorem requests_bounds (G : UniformGenerators α) (p : PolynomialBound) (n : ℕ) (bits : BitString) :
    (requests G p n bits).length≤n ∧ ∀ entry∈requests G p n bits,entry.2≤n := by
  have bounds := ExpectedStarSampling.chosenParts_bounds G p n bits
  refine ⟨by simpa only [requests,List.length_map] using bounds.1,?_⟩
  intro entry member
  change entry∈(ExpectedStarSampling.chosenParts G p n bits).map (fun j => (false,j)) at member
  obtain ⟨index,inParts,equal⟩ :=
    (List.mem_map (f := fun j : ℕ => (false,j)) (l := ExpectedStarSampling.chosenParts G p n bits)).mp member
  subst entry
  exact bounds.2 index inParts

abbrev DrawResult (p : PolynomialBound) (n : ℕ) :=
  ExpectedStarSampling.OuterRecord p n × List OriginalSourceFamilySampler.Record

def outputWord (G : UniformGenerators α) {p : PolynomialBound} {n : ℕ} (result : DrawResult p n) : List α :=
  OriginalSourceFamilySampler.words (families G) result.2
def sourceRuntime (G : UniformGenerators α) {p : PolynomialBound} {n : ℕ} (result : DrawResult p n) : ℕ :=
  OriginalSourceFamilySampler.totalTime (families G) result.2
def sourceCoins {p : PolynomialBound} {n : ℕ} (result : DrawResult p n) : ℕ :=
  OriginalSourceFamilySampler.consumed result.2
def outerOffset {p : PolynomialBound} {n : ℕ} (result : DrawResult p n) : ℕ :=
  (result.1.1+1)*StarCertification.width p n

variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

def draw (n : ℕ) (available : ExpectedStarSampling.Available G n) : FreshStreamSampler (DrawResult p n) :=
  (ExpectedStarSampling.outerCall G p expected n available).bind (fun record =>
    (OriginalSourceFamilySampler.calls (families G) (requests G p n (List.ofFn record.2))
      (requests_active G p n (List.ofFn record.2))).map (fun records => (record,records))
        (measurable_of_countable _))

theorem draw_lintegral (n : ℕ) (available : ExpectedStarSampling.Available G n)
    (value : DrawResult p n → ℝ≥0∞) :
    (∫⁻ stream,value (((draw G p expected n available).run stream).1)∂fairCoinMeasure)=
      ∫⁻ record, ∫⁻ future,value (record,
        ((OriginalSourceFamilySampler.calls (families G) (requests G p n (List.ofFn record.2))
          (requests_active G p n (List.ofFn record.2))).run future).1)∂fairCoinMeasure
            ∂(ExpectedStarSampling.outerCall G p expected n available).distribution := by
  exact FreshStreamSampler.lintegral_bind (ExpectedStarSampling.outerCall G p expected n available)
    (fun record => (OriginalSourceFamilySampler.calls (families G) (requests G p n (List.ofFn record.2))
      (requests_active G p n (List.ofFn record.2))).map (fun records => (record,records))
        (measurable_of_countable _)) value (measurable_of_countable _)

end
end ComplexityOfGenerators.ExpectedOriginalStarSampling
