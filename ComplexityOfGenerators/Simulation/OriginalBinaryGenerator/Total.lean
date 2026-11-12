import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Shape
import ComplexityOfGenerators.Simulation.OriginalHeaderController.NativeTotal
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.PrefixTail
import ComplexityOfGenerators.Proofs.OriginalSourceHookSupport

namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
open NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)

def layers : Operation→ℕ→Language α
  | .union => IndexedSupport.unionLayers (families false).layer (families true).layer
  | .concatenation => IndexedSupport.concatLayers (families false).layer (families true).layer

theorem choice_layers_of_calls (operation : Operation) (n : ℕ) (header : List Bool) (requests : List Request)
    (choice : OriginalHeaderController.Choice operation n header requests) (bits : BitString) (offset : ℕ)
    (records : List (Hook.CallRecord α))
    (calls : Hook.SourceCalls (OriginalSourceFamilySampler.source families) (OriginalSourceFamilySampler.entry families Prod.fst)
      bits offset (OriginalHeaderController.eventList requests) records) :
    Hook.words records∈layers families operation n := by
  cases operation with
  | union =>
      obtain ⟨tag,_,rfl⟩ := choice
      exact OriginalSourceFamilySampler.unionLayers_of_calls families bits offset n tag (decide (n=0)) records calls
  | concatenation =>
      obtain ⟨j,within,_,rfl⟩ := choice
      have member := OriginalSourceFamilySampler.concatLayers_of_calls families bits offset j (n-j)
        (decide (j=0)) (decide (n-j=0)) records calls
      simpa only [layers,Nat.add_sub_of_le within] using member

theorem machine_total (operation : Operation) (n : ℕ) (bits : BitString) :
    ∃ ticks result,(machine families p operation).run (generatorData n) bits ticks=.halted result ∧
      result≠.rejected ∧ ∀ word,result=.accepted word→word∈layers families operation n := by
  let C := controller families p operation
  let parameter := controllerParameter families p operation
  let M := OriginalSourceFamilySampler.source families
  let start : Event→Fin M.states := OriginalSourceFamilySampler.entry families Prod.fst
  change ∃ ticks result,(Hook.machine C M parameter start).run (generatorData n) bits ticks=.halted result ∧
    result≠.rejected ∧ ∀ word,result=.accepted word→word∈layers families operation n
  cases OriginalHeaderController.machine_split_total (selector families p operation) (width p operation)
      (selectorClock families p operation) operation n bits (controller_shape families p operation n) with
  | inl exhausted =>
      obtain ⟨ticks,last,path,empty,terminal⟩ := exhausted
      have run := Hook.prefix_exhausted C M parameter start (generatorData n) bits ticks last path empty terminal
      exact ⟨ticks,.exhausted,run,by simp,by intro word impossible;cases impossible⟩
  | inr selected =>
      obtain ⟨header,requests,choice,hit,prefixTicks,tailTicks,source,last,prefixPath,empty,trace,tail,stable,accepted⟩ := selected
      have bounded : ∀ entry∈OriginalHeaderController.eventList requests,entry.2≤n := by
        intro entry member
        obtain ⟨request,inside,rfl⟩ := List.mem_map.mp member
        exact choice.indices request inside
      have halting : ∀ entry∈OriginalHeaderController.eventList requests,
          (Hook.selectedSource M start entry.1).HaltingTransducer (generatorData entry.2) := by
        intro entry member
        exact OriginalSourceFamilySampler.selected_halting families Prod.fst entry.1 entry.2
      obtain ⟨ticks,result,run,noReject⟩ := Hook.prefix_tail_halts C M parameter start OriginalHeaderController.allowed
        (generatorData n) bits n (OriginalHeaderController.eventList requests) bounded prefixTicks source last
        prefixPath empty trace stable halting _ accepted
      refine ⟨ticks,result,run,noReject,?_⟩
      intro word resultEqual
      have produced : ∃ time,(Hook.machine C M parameter start).run (generatorData n) bits time=.halted (.accepted word) :=
        ⟨ticks,by simpa only [resultEqual] using run⟩
      obtain ⟨records,calls,equal⟩ := (Hook.prefix_tail_accepted_iff C M parameter start OriginalHeaderController.allowed
        (generatorData n) bits n (OriginalHeaderController.eventList requests) bounded prefixTicks tailTicks source last
        prefixPath empty trace tail stable halting _ accepted word).mp produced
      rw [equal]
      exact choice_layers_of_calls families operation n header requests choice bits source.randomHead records calls

theorem machine_halting (operation : Operation) (n : ℕ) :
    (machine families p operation).HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨ticks,result,run,_,_⟩ := machine_total families p operation n bits
    exact ⟨ticks,result,run⟩
  · intro bits ticks rejected
    obtain ⟨time,result,run,noReject,_⟩ := machine_total families p operation n bits
    exact noReject ((machine families p operation).halted_outcome_unique (generatorData n) bits time ticks _ _ run rejected)

theorem machine_language_subset (operation : Operation) (n : ℕ) :
    (machine families p operation).generatedLanguage (generatorData n)⊆layers families operation n := by
  intro word member
  obtain ⟨bits,ticks,produced⟩ := ((machine families p operation).mem_generatedLanguage_iff_produces (generatorData n) word).mp member
  obtain ⟨time,result,run,_,support⟩ := machine_total families p operation n bits
  exact support word ((machine families p operation).halted_outcome_unique (generatorData n) bits time ticks _ _ run produced)

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
