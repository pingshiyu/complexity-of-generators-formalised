import ComplexityOfGenerators.Proofs.OriginalSourceHookTrace
import ComplexityOfGenerators.Foundations.IndexedStarLanguage

/-! Accepted original calls give the exact indexed support of each closure
operation. These are consequences of actual native source paths. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

theorem starLayers_of_calls (G : UniformGenerators α) (bits : BitString) (offset n : ℕ)
    (parts : List ℕ) (records : List (NativeSourceCall.Hook.CallRecord α))
    (positive : ∀ j∈parts,0 < j) (total : parts.sum=n)
    (calls : NativeSourceCall.Hook.SourceCalls (source (fun _=>G)) (entry (fun _=>G) (fun _ : Unit=>false))
      bits offset (parts.map (fun j=>((),j))) records) :
    NativeSourceCall.Hook.words records∈IndexedSupport.starLayers G.layer n := by
  have members := sourceCalls_members (fun _=>G) (fun _ : Unit=>false) calls
  have sourceMembers : List.Forall₂ (fun j record => record.word∈G.layer j) parts records := by
    simpa only [List.forall₂_map_left_iff] using members
  have generated : List.Forall₂ (fun j word => 0 < j ∧ word∈G.layer j) parts (records.map NativeSourceCall.Hook.CallRecord.word) := by
    rw [List.forall₂_map_right_iff]
    clear total n calls members
    induction sourceMembers with
    | nil => exact .nil
    | @cons j record parts records first rest ih =>
        exact .cons ⟨positive j (by simp),first⟩ (ih (fun k belongs => positive k (by simp [belongs])))
  exact ⟨parts,records.map NativeSourceCall.Hook.CallRecord.word,generated,total,rfl⟩

theorem unionLayers_of_calls (families : Bool → UniformGenerators α) (bits : BitString) (offset n : ℕ)
    (tag zero : Bool) (records : List (NativeSourceCall.Hook.CallRecord α))
    (calls : NativeSourceCall.Hook.SourceCalls (source families) (entry families Prod.fst)
      bits offset [((tag,zero),n)] records) :
    NativeSourceCall.Hook.words records∈IndexedSupport.unionLayers (families false).layer (families true).layer n := by
  cases records with
  | nil => exact False.elim calls
  | cons record records =>
      cases records with
      | cons other records => exact False.elim calls.2
      | nil =>
          have member := callAt_member families Prod.fst bits offset (tag,zero) n record calls.1
          change record.word++[]∈(families false).layer n∪(families true).layer n
          rw [List.append_nil]
          cases tag
          · exact Or.inl member
          · exact Or.inr member

theorem concatLayers_of_calls (families : Bool → UniformGenerators α) (bits : BitString) (offset i j : ℕ)
    (leftZero rightZero : Bool) (records : List (NativeSourceCall.Hook.CallRecord α))
    (calls : NativeSourceCall.Hook.SourceCalls (source families) (entry families Prod.fst)
      bits offset [((false,leftZero),i),((true,rightZero),j)] records) :
    NativeSourceCall.Hook.words records∈IndexedSupport.concatLayers (families false).layer (families true).layer (i+j) := by
  cases records with
  | nil => exact False.elim calls
  | cons left records =>
      cases records with
      | nil => exact False.elim calls.2
      | cons right records =>
          cases records with
          | cons other records => exact False.elim calls.2.2
          | nil =>
              have leftMember := callAt_member families Prod.fst bits offset (false,leftZero) i left calls.1
              have rightMember := callAt_member families Prod.fst bits (offset+left.coins) (true,rightZero) j right calls.2.1
              exact ⟨i,j,rfl,left.word,leftMember,right.word,rightMember,by simp [NativeSourceCall.Hook.words]⟩

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
