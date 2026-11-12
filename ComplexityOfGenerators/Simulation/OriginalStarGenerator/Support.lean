import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Witness
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses
import ComplexityOfGenerators.Foundations.IndexedStarLanguage

/-! Every indexed star word has a genuine finite native witness. Only bounded
productivity certificates are capped; the selected source words are unrestricted. -/
namespace ComplexityOfGenerators.Simulation.OriginalStarGenerator
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

include expected in
theorem machine_language_superset (n : ℕ) : IndexedSupport.starLayers G.layer n⊆
    (machine G.machine p).generatedLanguage (generatorData n) := by
  rintro word ⟨parts,factors,generated,total,flattened⟩
  have active : ∀ j∈parts,0 < j ∧ (G.layer j).Nonempty := by
    clear total flattened n
    induction generated with
    | nil => simp
    | @cons j factor parts factors first rest ih =>
        intro k belongs
        rcases List.mem_cons.mp belongs with rfl|belongs
        · exact ⟨first.1,factor,first.2⟩
        · exact ih k belongs
  have available : CertifiedStarPhase.AvailableComposition G n parts := ⟨total,active⟩
  have members : List.Forall₂ (fun entry output => output∈(ExpectedOriginalStarSampling.families G entry.1).layer entry.2)
      (parts.map (fun j=>(false,j))) factors := by
    apply List.forall₂_map_left_iff.mpr
    exact List.Forall₂.imp (fun _ _ pair=>pair.2) generated
  obtain ⟨records,requests,outputs,minimal⟩ :=
    OriginalSourceFamilySampler.generated_records (ExpectedOriginalStarSampling.families G) _ _ members
  obtain ⟨bits,ticks,nonempty,_,run⟩ := runs_records G p expected n parts records available requests minimal
  exact ⟨bits,nonempty,ticks,by simpa only [outputs,flattened] using run⟩

end
end ComplexityOfGenerators.Simulation.OriginalStarGenerator
