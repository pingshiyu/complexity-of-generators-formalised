import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Witness
import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Total

/-! The actual native direct-call union and concatenation machines preserve
all original indexed words, including zero-index and arbitrarily long members. -/
namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
include expected

theorem machine_language_superset (operation : Operation) (n : ℕ) :
    layers families operation n⊆(machine families p operation).generatedLanguage (generatorData n) := by
  intro word member
  cases operation with
  | union =>
      have selected : ∃ tag,word∈(families tag).layer n := by
        rcases member with left|right
        · exact ⟨false,left⟩
        · exact ⟨true,right⟩
      obtain ⟨tag,member⟩ := selected
      have available : Available families .union n [(tag,n)] := ⟨tag,rfl,word,member⟩
      have members : List.Forall₂ (fun entry output=>output∈(families entry.1).layer entry.2) [(tag,n)] [word] := .cons member .nil
      obtain ⟨records,labels,outputs,minimal⟩ := OriginalSourceFamilySampler.generated_records families _ _ members
      obtain ⟨bits,ticks,nonempty,time,run⟩ := runs_records families p expected .union n _ records available labels minimal
      refine ⟨bits,nonempty,ticks,?_⟩
      simpa only [outputs,List.flatten_cons,List.flatten_nil,List.append_nil] using run
  | concatenation =>
      obtain ⟨left,right,total,u,leftMember,v,rightMember,equal⟩ := member
      subst n
      have available : Available families .concatenation (left+right) [(false,left),(true,right)] := by
        refine ⟨left,by omega,?_,⟨u,leftMember⟩,?_⟩
        · simp
        · simpa using (show ((families true).layer right).Nonempty from ⟨v,rightMember⟩)
      have members : List.Forall₂ (fun entry output=>output∈(families entry.1).layer entry.2)
          [(false,left),(true,right)] [u,v] := .cons leftMember (.cons rightMember .nil)
      obtain ⟨records,labels,outputs,minimal⟩ := OriginalSourceFamilySampler.generated_records families _ _ members
      obtain ⟨bits,ticks,nonempty,time,run⟩ := runs_records families p expected .concatenation (left+right) _ records available labels minimal
      refine ⟨bits,nonempty,ticks,?_⟩
      simpa only [outputs,List.flatten_cons,List.flatten_nil,List.append_nil,equal] using run

theorem machine_language (operation : Operation) (n : ℕ) :
    (machine families p operation).generatedLanguage (generatorData n)=layers families operation n :=
  Set.Subset.antisymm (machine_language_subset families p operation n) (machine_language_superset families p expected operation n)

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
