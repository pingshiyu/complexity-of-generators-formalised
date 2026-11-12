import ComplexityOfGenerators.Proofs.OriginalSourceClosureSupport
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses
import ComplexityOfGenerators.Proofs.ExpectedOriginalStarSampling.Basic

/-! Global lucky witnesses retain the actual consumed source prefixes. Their
total source runtime and total producing index are polynomial in the final
word length, without any bound on other members of those source layers. -/
namespace ComplexityOfGenerators.OriginalSourceClosure
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

def wordWork (q : PolynomialBound) : PolynomialBound := (⟨2,1,by decide⟩ : PolynomialBound).mul q

theorem star_fast_records (G : UniformGenerators α) (mean : G.ExpectedLength)
    (fast : G.GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ word∈IndexedSupport.star G.language,
      ∃ n : ℕ,∃ parts : List ℕ,∃ records : List OriginalSourceFamilySampler.Record,
        n≤IndexedSupport.starBound q word.length ∧
        CertifiedStarPhase.AvailableComposition G n parts ∧
        records.map OriginalSourceFamilySampler.request=parts.map (fun j=>(false,j)) ∧
        (∀ record∈records,OriginalSourceFamilySampler.MinimalRecord (ExpectedOriginalStarSampling.families G) record) ∧
        OriginalSourceFamilySampler.words (ExpectedOriginalStarSampling.families G) records=word ∧
        OriginalSourceFamilySampler.totalTime (ExpectedOriginalStarSampling.families G) records+records.length≤wordWork q word.length := by
  obtain ⟨q,paths⟩ := star_fast_factors G mean fast
  refine ⟨q,?_⟩
  intro word member
  obtain ⟨requests,factors,flattened,count,sumBound,valid⟩ := paths word member
  let parts := requests.map Prod.fst
  let sourceRequests := requests.map (fun request=>(false,request.1))
  have sourcePaths : List.Forall₂
      (OriginalSourceFamilySampler.WordPath (ExpectedOriginalStarSampling.families G) (q word.length))
      sourceRequests factors := by
    apply List.forall₂_map_left_iff.mpr
    exact List.Forall₂.imp (fun request factor generated=>⟨request.2,generated.2.2⟩) valid
  obtain ⟨records,labels,outputs,minimal,timeBound⟩ := OriginalSourceFamilySampler.bounded_records
    (ExpectedOriginalStarSampling.families G) (q word.length) sourceRequests factors sourcePaths
  have active : ∀ request∈requests,0 < request.1 ∧ (G.layer request.1).Nonempty := by
    clear sumBound count flattened sourcePaths labels outputs minimal timeBound
    induction valid with
    | nil => simp
    | @cons request factor requests factors first rest ih =>
        intro r belongs
        rcases List.mem_cons.mp belongs with rfl|belongs
        · exact ⟨first.1,factor,r.2,first.2.1,q word.length,first.2.2⟩
        · exact ih r belongs
  have available : CertifiedStarPhase.AvailableComposition G parts.sum parts := by
    refine ⟨rfl,?_⟩
    intro j belongs
    obtain ⟨request,inside,rfl⟩ := List.mem_map.mp belongs
    exact active request inside
  have recordedCount : records.length=requests.length := by
    have equal := congrArg List.length labels
    simpa only [List.length_map,sourceRequests] using equal
  have originalTime : OriginalSourceFamilySampler.totalTime (ExpectedOriginalStarSampling.families G) records≤word.length*q word.length := by
    apply timeBound.trans
    simpa only [sourceRequests,List.length_map] using Nat.mul_le_mul_right (q word.length) count
  refine ⟨parts.sum,parts,records,sumBound,available,?_,minimal,outputs.trans flattened,?_⟩
  · simpa only [parts,sourceRequests,List.map_map,Function.comp_def] using labels
  · rw [wordWork,PolynomialBound.mul_eval]
    change _≤2*(word.length+1)^1*q word.length
    rw [pow_one]
    have positive := q.positive word.length
    rw [recordedCount]
    nlinarith

end
end ComplexityOfGenerators.OriginalSourceClosure
