import ComplexityOfGenerators.Proofs.AlphabetGeneration
import ComplexityOfGenerators.Proofs.ExpectedNonclosure

namespace ComplexityOfGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

namespace AlphabetGeneration

theorem bool_retract [Nontrivial α] :
    ∃ encode : Bool→α,∃ decode : α→Bool,Function.LeftInverse decode encode := by
  classical
  obtain ⟨zero,one,different⟩ := exists_pair_ne α
  refine ⟨fun bit=>if bit then one else zero,fun letter=>decide (letter=one),?_⟩
  intro bit
  cases bit <;>simp [different,different.symm]

theorem infinite_intersection_transport
    (C : LanguageClass Bool) (D : LanguageClass α) (encode : Bool→α) (decode : α→Bool)
    (retract : Function.LeftInverse decode encode)
    (forward : ∀ L : Language Bool,L.Infinite → L∈C → List.map encode '' L∈D)
    (backward : ∀ L : Language α,(List.map decode '' L).Infinite → L∈D → List.map decode '' L∈C)
    (witness : ∃ A B : Language Bool,A∈C ∧ B∈C ∧ (A∩B).Infinite ∧ A∩B∉C) :
    ∃ A B : Language α,A∈D ∧ B∈D ∧ (A∩B).Infinite ∧ A∩B∉D := by
  obtain ⟨A,B,left,right,infinite,outside⟩ := witness
  have wordRetract : Function.LeftInverse (List.map decode) (List.map encode) := by
    intro word
    have pointwise : (fun bit=>decode (encode bit))=id := funext retract
    rw [List.map_map]
    change (List.map (fun bit=>decode (encode bit)) word)=word
    rw [pointwise,List.map_id]
  have injective : Function.Injective (List.map encode) := wordRetract.injective
  have intersection : List.map encode '' A∩List.map encode '' B=List.map encode '' (A∩B) :=
    (Set.image_inter injective).symm
  have restored (L : Language Bool) : List.map decode '' (List.map encode '' L)=L := by
    rw [Set.image_image]
    have composition : (fun word=>List.map decode (List.map encode word))=id := funext wordRetract
    rw [composition,Set.image_id]
  have decoded : List.map decode '' (List.map encode '' A∩List.map encode '' B)=A∩B := by
    rw [intersection,restored]
  refine ⟨List.map encode '' A,List.map encode '' B,
    forward A (infinite.mono Set.inter_subset_left) left,
    forward B (infinite.mono Set.inter_subset_right) right,?_,?_⟩
  · rw [intersection]
    exact infinite.image injective.injOn
  · intro member
    have source := backward _ (by rw [decoded];exact infinite) member
    rw [decoded] at source
    exact outside source

end AlphabetGeneration

theorem pg_infinite_intersection_witness_alphabet [Nontrivial α]
    (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language α,A∈PG α ∧ B∈PG α ∧ (A∩B).Infinite ∧ A∩B∉PG α := by
  obtain ⟨encode,decode,retract⟩ := AlphabetGeneration.bool_retract (α:=α)
  exact AlphabetGeneration.infinite_intersection_transport (PG Bool) (PG α) encode decode retract
    (fun L _ member=>AlphabetGeneration.pg_image encode member)
    (fun L _ member=>AlphabetGeneration.pg_image decode member)
    (pg_infinite_intersection_witness hashes)

theorem epg_infinite_intersection_witness_alphabet [Nontrivial α]
    (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language α,A∈EPG α ∧ B∈EPG α ∧ (A∩B).Infinite ∧ A∩B∉EPG α := by
  obtain ⟨encode,decode,retract⟩ := AlphabetGeneration.bool_retract (α:=α)
  exact AlphabetGeneration.infinite_intersection_transport (EPG Bool) (EPG α) encode decode retract
    (fun L _ member=>AlphabetGeneration.epg_image encode member)
    (fun L _ member=>AlphabetGeneration.epg_image decode member)
    (epg_infinite_intersection_witness hashes)

theorem elepg_infinite_intersection_witness_alphabet [Nontrivial α]
    (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language α,A∈ELEPG α ∧ B∈ELEPG α ∧ (A∩B).Infinite ∧ A∩B∉ELEPG α := by
  obtain ⟨encode,decode,retract⟩ := AlphabetGeneration.bool_retract (α:=α)
  have injective : Function.Injective (List.map encode) := List.map_injective_iff.mpr retract.injective
  exact AlphabetGeneration.infinite_intersection_transport (ELEPG Bool) (ELEPG α) encode decode retract
    (fun L infinite member=>AlphabetGeneration.elepg_image encode (infinite.image injective.injOn) member)
    (fun L infinite member=>AlphabetGeneration.elepg_image decode infinite member)
    (elepg_infinite_intersection_witness hashes)

theorem pg_not_intersection_closed_alphabet [Nontrivial α] (hashes : CollisionResistantHashFunctionsExist) :
    ¬ClosedUnderIntersection (PG α) := by
  obtain ⟨A,B,left,right,_,outside⟩ := pg_infinite_intersection_witness_alphabet (α:=α) hashes
  exact fun closed=>outside (closed A B left right)

theorem epg_not_intersection_closed_alphabet [Nontrivial α] (hashes : CollisionResistantHashFunctionsExist) :
    ¬ClosedUnderIntersection (EPG α) := by
  obtain ⟨A,B,left,right,_,outside⟩ := epg_infinite_intersection_witness_alphabet (α:=α) hashes
  exact fun closed=>outside (closed A B left right)

theorem elepg_not_intersection_closed_alphabet [Nontrivial α] (hashes : CollisionResistantHashFunctionsExist) :
    ¬ClosedUnderIntersection (ELEPG α) := by
  obtain ⟨A,B,left,right,_,outside⟩ := elepg_infinite_intersection_witness_alphabet (α:=α) hashes
  exact fun closed=>outside (closed A B left right)

end
end ComplexityOfGenerators
