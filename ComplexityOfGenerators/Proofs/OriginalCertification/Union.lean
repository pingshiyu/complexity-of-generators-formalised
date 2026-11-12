import ComplexityOfGenerators.Proofs.OriginalCertification.Basic

/-! Union selects a productive tag using two bounded native certificates.
The successful tag is used only for a subsequent fresh ORIGINAL source call. -/
namespace ComplexityOfGenerators.OriginalCertification.Union
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α) (p : PolynomialBound)

def payload (tag : Bool) : List Unit := if tag then [()] else []
def phase (n : ℕ) : FiniteBlockPhase Unit :=
  FiniteBlockPhase.combine (marker (source (families false).machine p n) (payload false))
    (marker (source (families true).machine p n) (payload true))
def width : PolynomialBound := ⟨9*p.coefficient,p.degree,Nat.mul_pos (by decide) p.coefficient_pos⟩
@[simp] theorem width_eval (n : ℕ) : width p n=9*p n := by
  simp [width,PolynomialBound.eval,Nat.mul_assoc]
theorem width_fits (n : ℕ) : (phase families p n).width≤width p n := by
  have positive := p.positive n
  change seed p n+(seed p n+1)≤width p n
  rw [seed_eval,width_eval]
  omega

def value (n : ℕ) (bits : BitString) : Option (List Unit) := (phase families p n).evaluate bits
def choice (n : ℕ) (bits : BitString) : Option Bool :=
  (value families p n bits).map (fun word => decide (word.length=1))

variable (expected : ∀ tag j,((families tag).layer j).Nonempty →
  (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
include expected

theorem phase_language (n : ℕ) (word : List Unit) :
    word∈(phase families p n).language ↔
      ∃ tag,word=payload tag ∧ ((families tag).layer n).Nonempty := by
  rw [phase,FiniteBlockPhase.combine_language,marker_language,marker_language,
    source_positive_iff (families false) p n (expected false n),
    source_positive_iff (families true) p n (expected true n)]
  constructor
  · rintro (left|right)
    · exact ⟨false,left⟩
    · exact ⟨true,right⟩
  · rintro ⟨tag,valid⟩
    cases tag
    · exact Or.inl valid
    · exact Or.inr valid

theorem value_sound (n : ℕ) (bits : BitString) {word : List Unit}
    (result : value families p n bits=some word) :
    ∃ tag,word=payload tag ∧ ((families tag).layer n).Nonempty := by
  apply (phase_language families p expected n word).mp
  have enough : (phase families p n).width≤bits.length := by
    by_contra absent
    simp only [value,FiniteBlockPhase.evaluate,dite_eq_right absent] at result
    cases result
  change 0<fairBlockMeasure (phase families p n).width {block | (phase families p n).value block=some word}
  apply (fairBlockMeasure_event_pos_iff _ _).mpr
  exact ⟨FiniteBlockPhase.sample bits _ enough,by
    simpa only [Set.mem_ofPred_eq,value,FiniteBlockPhase.evaluate_eq _ _ enough] using result⟩

theorem choice_sound (n : ℕ) (bits : BitString) {tag : Bool}
    (result : choice families p n bits=some tag) : ((families tag).layer n).Nonempty := by
  obtain ⟨word,produced,selected⟩ := Option.map_eq_some_iff.mp result
  obtain ⟨found,equal,active⟩ := value_sound families p expected n bits produced
  subst word
  have same : found=tag := by cases found <;> simpa [payload] using selected
  exact same ▸ active

theorem phase_mass (n : ℕ)
    (available : ∃ tag,((families tag).layer n).Nonempty) :
    (1 : ℝ≥0∞)/2≤(phase families p n).successMass := by
  obtain ⟨tag,active⟩ := available
  have lower := source_mass (families tag).machine p n (expected tag n active)
  cases tag
  · calc
      _ ≤ (source (families false).machine p n).successMass := lower
      _ = (marker (source (families false).machine p n) (payload false)).successMass := (marker_success _ _).symm
      _ ≤ _ := FiniteBlockPhase.combine_success_ge_left _ _
  · calc
      _ ≤ (source (families true).machine p n).successMass := lower
      _ = (marker (source (families true).machine p n) (payload true)).successMass := (marker_success _ _).symm
      _ ≤ _ := FiniteBlockPhase.combine_success_ge_right _ _

theorem choice_mass (n : ℕ) (available : ∃ tag,((families tag).layer n).Nonempty) :
    (1 : ℝ≥0∞)/2≤fairBlockMeasure (width p n) {bits | (choice families p n (List.ofFn bits)).isSome} := by
  have law := FiniteBlockPhase.evaluate_event_measure (phase families p n) (width p n) (width_fits families p n)
    (fun output => output.isSome=true)
  have same : {bits : Fin (width p n) → Bool | (choice families p n (List.ofFn bits)).isSome}=
      {bits | ((phase families p n).evaluate (List.ofFn bits)).isSome} := by
    ext bits
    simp [choice,value]
  rw [same,law]
  exact phase_mass families p expected n available

theorem choice_support (n : ℕ) (tag : Bool) :
    (0<fairBlockMeasure (width p n) {bits | choice families p n (List.ofFn bits)=some tag}) ↔
      ((families tag).layer n).Nonempty := by
  constructor
  · intro positive
    obtain ⟨bits,result⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
    exact choice_sound families p expected n (List.ofFn bits) result
  · intro active
    have supported := (phase_language families p expected n (payload tag)).mpr ⟨tag,rfl,active⟩
    have law := FiniteBlockPhase.evaluate_event_measure (phase families p n) (width p n) (width_fits families p n)
      (fun output => output=some (payload tag))
    have positive : 0<fairBlockMeasure (width p n) {bits | value families p n (List.ofFn bits)=some (payload tag)} := by
      change 0<fairBlockMeasure (width p n) {bits | (phase families p n).evaluate (List.ofFn bits)=some (payload tag)}
      rw [law]
      exact supported
    obtain ⟨bits,result⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
    change value families p n (List.ofFn bits)=some (payload tag) at result
    apply (fairBlockMeasure_event_pos_iff _ _).mpr
    refine ⟨bits,?_⟩
    change choice families p n (List.ofFn bits)=some tag
    unfold choice
    rw [result]
    cases tag <;> simp [payload]

end
end ComplexityOfGenerators.OriginalCertification.Union
