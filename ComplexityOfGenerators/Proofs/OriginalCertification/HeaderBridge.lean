import ComplexityOfGenerators.Foundations.FiniteBlockPhaseMaps
import ComplexityOfGenerators.Proofs.OriginalCertification.Union
import ComplexityOfGenerators.Proofs.OriginalCertification.Concatenation
import ComplexityOfGenerators.Simulation.UnionGenerator.PhaseMeans
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.PhaseMeans

/-! Semantic bridge for genuine bounded header certifiers. The premises are
the concrete `BoundedHeaderCertification.native_view` equations; these lemmas
only transport those equations through the existing native selection policy. -/
namespace ComplexityOfGenerators.OriginalCertification.HeaderBridge
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type}

def header (tag : Bool) (index : ℕ) : List Bool := List.replicate (index+1) tag
def concatHeader (n j : ℕ) : List Bool := header false j++header true (n-j)
def unionTransform (n : ℕ) (word : List Unit) : List Bool := header (decide (word.length=1)) n
def concatTransform (n : ℕ) (word : List Unit) : List Bool := concatHeader n word.length

def View (original : Machine Unit Bool α) (certificate : Machine Unit Bool Bool) (tag : Bool)
    (p time : PolynomialBound) : Prop :=
  ∀ j bits,bits.length=seed p j → UnionGenerator.sourceValue certificate time j bits=
    (UnionGenerator.sourceValue original (clock p) j bits).map (fun _ => header tag j)

theorem source_phase_eq (original : Machine Unit Bool α) (certificate : Machine Unit Bool Bool) (tag : Bool)
    (p time : PolynomialBound) (view : View original certificate tag p time) (j : ℕ) :
    UnionGenerator.sourcePhase certificate (seed p) time j=marker (source original p j) (header tag j) := by
  apply congrArg (fun value => (⟨seed p j,value⟩ : FiniteBlockPhase Bool))
  funext bits
  exact view j (List.ofFn bits) (by simp)

theorem union_phase_eq (families : Bool → UniformGenerators α) (left right : Machine Unit Bool Bool)
    (p leftTime rightTime : PolynomialBound)
    (leftView : View (families false).machine left false p leftTime)
    (rightView : View (families true).machine right true p rightTime) (n : ℕ) :
    UnionGenerator.offerPhase left right (seed p) leftTime (seed p) rightTime n=
      (Union.phase families p n).relabel (unionTransform n) := by
  change FiniteBlockPhase.combine (UnionGenerator.sourcePhase left (seed p) leftTime n)
    (UnionGenerator.sourcePhase right (seed p) rightTime n)=_
  rw [source_phase_eq _ _ _ _ _ leftView,source_phase_eq _ _ _ _ _ rightView]
  rw [Union.phase,FiniteBlockPhase.relabel_combine]
  change FiniteBlockPhase.combine _ _=FiniteBlockPhase.combine
    (((source (families false).machine p n).relabel (fun _ => Union.payload false)).relabel (unionTransform n))
    (((source (families true).machine p n).relabel (fun _ => Union.payload true)).relabel (unionTransform n))
  rw [FiniteBlockPhase.relabel_marker,FiniteBlockPhase.relabel_marker]
  rfl

/-- The old native union value returns exactly the header for the selected
productive tag, on the same full random block and selector coin. -/
theorem union_value (families : Bool → UniformGenerators α) (left right : Machine Unit Bool Bool)
    (p leftTime rightTime : PolynomialBound)
    (leftView : View (families false).machine left false p leftTime)
    (rightView : View (families true).machine right true p rightTime)
    (n : ℕ) (bits : BitString) (enough : Union.width p n≤bits.length) :
    UnionGenerator.value left right (seed p) leftTime (seed p) rightTime n bits=
      (Union.choice families p n bits).map (fun tag => header tag n) := by
  have phases := union_phase_eq families left right p leftTime rightTime leftView rightView n
  have fits : (UnionGenerator.offerPhase left right (seed p) leftTime (seed p) rightTime n).width≤bits.length := by
    rw [phases]
    exact (Union.width_fits families p n).trans enough
  rw [UnionGenerator.value_eq_offerPhase left right (seed p) leftTime (seed p) rightTime n bits fits,
    phases,FiniteBlockPhase.evaluate_relabel]
  simp only [Union.choice,Union.value,Option.map_map,Function.comp_def]
  rfl

theorem candidate_phase_eq (families : Bool → UniformGenerators α) (left right : Machine Unit Bool Bool)
    (p leftTime rightTime : PolynomialBound)
    (leftView : View (families false).machine left false p leftTime)
    (rightView : View (families true).machine right true p rightTime) (n j : ℕ) :
    ConcatenationGenerator.candidatePhase left right (seed p) leftTime (seed p) rightTime n j=
      (Concatenation.candidate families p n j).relabel (concatTransform n) := by
  change FiniteBlockPhase.concatenate (UnionGenerator.sourcePhase left (seed p) leftTime j)
    (UnionGenerator.sourcePhase right (seed p) rightTime (n-j))=_
  rw [source_phase_eq _ _ _ _ _ leftView,source_phase_eq _ _ _ _ _ rightView]
  change FiniteBlockPhase.concatenate
    ((source (families false).machine p j).relabel (fun _ => header false j))
    ((source (families true).machine p (n-j)).relabel (fun _ => header true (n-j)))=_
  rw [FiniteBlockPhase.concatenate_markers]
  change _=((FiniteBlockPhase.concatenate (source (families false).machine p j)
    (source (families true).machine p (n-j))).relabel (fun _ => List.replicate j ())).relabel (concatTransform n)
  rw [FiniteBlockPhase.relabel_marker]
  simp only [concatTransform,List.length_replicate,concatHeader]

theorem concat_phase_eq (families : Bool → UniformGenerators α) (left right : Machine Unit Bool Bool)
    (p leftTime rightTime : PolynomialBound)
    (leftView : View (families false).machine left false p leftTime)
    (rightView : View (families true).machine right true p rightTime) (n : ℕ) :
    ConcatenationGenerator.scanPhase left right (seed p) leftTime (seed p) rightTime n=
      (Concatenation.phase families p n).relabel (concatTransform n) := by
  rw [Concatenation.phase,FiniteBlockPhase.relabel_scan]
  change FiniteBlockPhase.scan ((List.range (n+1)).map
    (ConcatenationGenerator.candidatePhase left right (seed p) leftTime (seed p) rightTime n))=
      FiniteBlockPhase.scan (((List.range (n+1)).map (Concatenation.candidate families p n)).map
        (fun phase => phase.relabel (concatTransform n)))
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact candidate_phase_eq families left right p leftTime rightTime leftView rightView n j

/-- The existing all-splits native algorithm returns exactly the header of
the selected split. No change to its fair offer or scan order is required. -/
theorem concat_value (families : Bool → UniformGenerators α) (left right : Machine Unit Bool Bool)
    (p leftTime rightTime : PolynomialBound)
    (leftView : View (families false).machine left false p leftTime)
    (rightView : View (families true).machine right true p rightTime)
    (n : ℕ) (bits : BitString) (enough : Concatenation.width p n≤bits.length) :
    ConcatenationGenerator.algorithm left right (seed p) leftTime (seed p) rightTime n bits=
      (Concatenation.choice families p n bits).map (concatHeader n) := by
  have phases := concat_phase_eq families left right p leftTime rightTime leftView rightView n
  have fits : (ConcatenationGenerator.scanPhase left right (seed p) leftTime (seed p) rightTime n).width≤bits.length := by
    rw [phases]
    exact (Concatenation.width_fits families p n).trans enough
  rw [ConcatenationGenerator.algorithm_eq_scanPhase left right (seed p) leftTime (seed p) rightTime n bits fits,
    phases,FiniteBlockPhase.evaluate_relabel]
  simp only [Concatenation.choice,Concatenation.value,Option.map_map,Function.comp_def]
  rfl

end
end ComplexityOfGenerators.OriginalCertification.HeaderBridge
