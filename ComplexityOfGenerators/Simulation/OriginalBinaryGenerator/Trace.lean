import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Shape
import ComplexityOfGenerators.Simulation.OriginalHeaderController.NativeSplit
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.PrefixTail

namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
open NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound) (operation : Operation)

theorem machine_runs_trace (n failures : ℕ) (bits : BitString) (header : List Bool) (requests : List Request)
    (records : List OriginalSourceFamilySampler.Record)
    (choice : OriginalHeaderController.Choice operation n header requests)
    (enough : (failures+1)*width p operation n≤bits.length)
    (failed : ∀ k<failures,reference families p operation n ((bits.drop (k*width p operation n)).take (width p operation n))=none)
    (accepted : reference families p operation n ((bits.drop (failures*width p operation n)).take (width p operation n))=some header)
    (sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace families bits ((failures+1)*width p operation n) requests records) :
    ∃ticks,ticks≤25*(coefficient families p operation n)^2*(failures+1)^2+
        (6*n+20)*(OriginalSourceFamilySampler.totalTime families records+records.length) ∧
      (machine families p operation).run (generatorData n) bits ticks=
        .halted (.accepted (OriginalSourceFamilySampler.words families records)) := by
  let C := controller families p operation
  let parameter := controllerParameter families p operation
  let M := OriginalSourceFamilySampler.source families
  let start : Event→Fin M.states := OriginalSourceFamilySampler.entry families Prod.fst
  obtain ⟨prefixTicks,tailTicks,tailStart,last,head,empty,cursor,trace,tail,stable,terminal,budget⟩ :=
    OriginalHeaderController.machine_split_success (selector families p operation) (width p operation)
      (selectorClock families p operation) operation n failures bits header requests choice enough failed accepted
  have calls := OriginalSourceFamilySampler.finiteSequenceTrace_hook families Prod.fst bits
    ((failures+1)*width p operation n) requests records (OriginalHeaderController.eventList requests) sourceTrace (by
      simp [OriginalHeaderController.eventList,List.map_map,Function.comp_def])
  rw [←cursor] at calls
  have indices : ∀ entry∈OriginalHeaderController.eventList requests,entry.2≤n := by
    intro entry member
    obtain ⟨request,inside,rfl⟩ := List.mem_map.mp member
    exact choice.indices request inside
  obtain ⟨ticks,time,run⟩ := Hook.prefix_tail_accept C M parameter start OriginalHeaderController.allowed
    (generatorData n) bits n (OriginalHeaderController.eventList requests) indices
    (records.map (OriginalSourceFamilySampler.hookRecord families)) prefixTicks tailTicks tailStart last
    head empty trace tail stable calls _ terminal
  refine ⟨ticks,?_,?_⟩
  · simp only [OriginalSourceFamilySampler.hookRecord_time,List.length_map] at time
    change prefixTicks+tailTicks≤25*(coefficient families p operation n)^2*(failures+1)^2 at budget
    omega
  · simpa only [machine,C,M,parameter,start,OriginalSourceFamilySampler.hookRecord_words] using run

/-- The actual selector and the probabilistic request sampler use identical
random blocks; the header encoding only prepares the native call events. -/
theorem machine_runs_selection_trace (n failures : ℕ) (bits : BitString) (requests : List Request)
    (records : List OriginalSourceFamilySampler.Record)
    (enough : (failures+1)*width p operation n≤bits.length)
    (failed : ∀ k<failures,selection families p operation n ((bits.drop (k*width p operation n)).take (width p operation n))=none)
    (selected : selection families p operation n ((bits.drop (failures*width p operation n)).take (width p operation n))=some requests)
    (sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace families bits ((failures+1)*width p operation n) requests records) :
    ∃ticks,ticks≤25*(coefficient families p operation n)^2*(failures+1)^2+
        (6*n+20)*(OriginalSourceFamilySampler.totalTime families records+records.length) ∧
      (machine families p operation).run (generatorData n) bits ticks=
        .halted (.accepted (OriginalSourceFamilySampler.words families records)) := by
  have full : ∀ k≤failures, ((bits.drop (k*width p operation n)).take (width p operation n)).length=width p operation n := by
    intro k within
    have available := (Nat.mul_le_mul_right (width p operation n) (Nat.add_le_add_right within 1)).trans enough
    simp only [List.length_take,List.length_drop]
    have availableSum : k*width p operation n+width p operation n≤bits.length := by
      simpa only [Nat.add_mul,Nat.one_mul] using available
    have limit : width p operation n≤bits.length-k*width p operation n := by omega
    exact Nat.min_eq_left limit
  apply machine_runs_trace families p operation n failures bits (headerOf operation n requests) requests records
    (selection_choice families p operation n _ requests selected) enough _ _ sourceTrace
  · intro k within
    rw [reference_view families p operation n _ (full k (by omega)),failed k within,Option.map_none]
  · rw [reference_view families p operation n _ (full failures le_rfl),selected,Option.map_some]

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
