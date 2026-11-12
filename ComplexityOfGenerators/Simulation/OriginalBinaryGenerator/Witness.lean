import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Trace
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses

/-! Every supported binary request list has one bounded certificate block and
actual unbounded original-source prefixes. Only certificates are capped. -/
namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)

def Available : Operation→ℕ→List Request→Prop
  | .union,n,requests => ∃ tag,requests=[(tag,n)] ∧ ((families tag).layer n).Nonempty
  | .concatenation,n,requests => ∃ index,index≤n ∧ requests=[(false,index),(true,n-index)] ∧
      ((families false).layer index).Nonempty ∧ ((families true).layer (n-index)).Nonempty

variable (expected : ∀ tag j,((families tag).layer j).Nonempty →
  (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
include expected

theorem selection_support (operation : Operation) (n : ℕ) (requests : List Request)
    (available : Available families operation n requests) :
    ∃ block : BitString,block.length=width p operation n ∧ selection families p operation n block=some requests := by
  cases operation with
  | union =>
      obtain ⟨tag,rfl,active⟩ := available
      have positive := (OriginalCertification.Union.choice_support families p expected n tag).mpr active
      obtain ⟨bits,produced⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
      refine ⟨List.ofFn bits,by simp [width,ExpectedOriginalBinarySampling.width],?_⟩
      change OriginalCertification.Union.choice families p n (List.ofFn bits)=some tag at produced
      simp only [selection,ExpectedOriginalBinarySampling.selection,ExpectedOriginalUnionSampling.selection,
        ExpectedOriginalConcatenationSampling.selection,produced,Option.map_some]
  | concatenation =>
      obtain ⟨index,within,rfl,left,right⟩ := available
      have positive := (OriginalCertification.Concatenation.choice_support families p expected n index).mpr ⟨within,left,right⟩
      obtain ⟨bits,produced⟩ := (fairBlockMeasure_event_pos_iff _ _).mp positive
      refine ⟨List.ofFn bits,by simp [width,ExpectedOriginalBinarySampling.width],?_⟩
      change OriginalCertification.Concatenation.choice families p n (List.ofFn bits)=some index at produced
      simp only [selection,ExpectedOriginalBinarySampling.selection,ExpectedOriginalUnionSampling.selection,
        ExpectedOriginalConcatenationSampling.selection,produced,Option.map_some]

theorem runs_records (operation : Operation) (n : ℕ) (requests : List Request)
    (records : List OriginalSourceFamilySampler.Record) (available : Available families operation n requests)
    (labels : records.map OriginalSourceFamilySampler.request=requests)
    (minimal : ∀ record∈records,OriginalSourceFamilySampler.MinimalRecord families record) :
    ∃ bits ticks,bits≠[] ∧
      ticks≤25*(coefficient families p operation n)^2+
        (6*n+20)*(OriginalSourceFamilySampler.totalTime families records+records.length) ∧
      (machine families p operation).run (generatorData n) bits ticks=
        .halted (.accepted (OriginalSourceFamilySampler.words families records)) := by
  obtain ⟨block,length,selected⟩ := selection_support families p expected operation n requests available
  let bits := block++OriginalSourceFamilySampler.seedWord records
  have sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace families bits (width p operation n) requests records := by
    have actual := OriginalSourceFamilySampler.records_finiteTrace families records minimal block []
    simpa only [List.append_nil,length,labels] using actual
  have taken : bits.take (width p operation n)=block := by
    dsimp only [bits]
    rw [←length,List.take_left]
  have enough : (0+1)*width p operation n≤bits.length := by
    simp only [Nat.zero_add,Nat.one_mul,bits,List.length_append,length]
    omega
  obtain ⟨ticks,time,run⟩ := machine_runs_selection_trace families p operation n 0 bits requests records enough
    (by intro k before;omega) (by simpa only [Nat.zero_mul,List.drop_zero,taken] using selected)
    (by simpa only [Nat.zero_add,Nat.one_mul] using sourceTrace)
  have nonempty : bits≠[] := by
    intro empty
    have sizes := congrArg List.length empty
    simp only [bits,List.length_append,length,List.length_nil] at sizes
    have positive := (width p operation).positive n
    omega
  exact ⟨bits,ticks,nonempty,by simpa only [Nat.zero_add,Nat.one_pow,Nat.mul_one] using time,run⟩

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
