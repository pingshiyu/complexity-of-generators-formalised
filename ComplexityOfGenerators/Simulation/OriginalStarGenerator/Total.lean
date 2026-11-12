import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Basic
import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.NativeTotal
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.PrefixTail
import ComplexityOfGenerators.Proofs.OriginalSourceHookSupport
import ComplexityOfGenerators.Proofs.ExpectedOriginalStarSampling.Basic

/-! Every finite seed of the actual native star generator terminates without
explicit rejection. Every accepted output is a genuine concatenation of
original source words with positive layer indices summing to the target. -/
namespace ComplexityOfGenerators.Simulation.OriginalStarGenerator
open NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)

theorem machine_total (n : ℕ) (bits : BitString) :
    ∃ ticks result,(machine G.machine p).run (generatorData n) bits ticks=.halted result ∧
      result≠.rejected ∧ ∀ word,result=.accepted word→word∈IndexedSupport.starLayers G.layer n := by
  let C := ExpectedOriginalStarController.machine G.machine p
  let parameter := ExpectedOriginalStarController.parameter G.machine p
  let families := ExpectedOriginalStarSampling.families G
  let M := OriginalSourceFamilySampler.source families
  let start : Unit → Fin M.states := OriginalSourceFamilySampler.entry families (fun _=>false)
  change ∃ ticks result,(Hook.machine C M parameter start).run (generatorData n) bits ticks=.halted result ∧
    result≠.rejected ∧ ∀ word,result=.accepted word→word∈IndexedSupport.starLayers G.layer n
  cases ExpectedOriginalStarController.machine_split_total G.machine p n bits with
  | inl exhausted =>
      obtain ⟨ticks,last,path,empty,terminal⟩ := exhausted
      have run := Hook.prefix_exhausted C M parameter start (generatorData n) bits ticks last path empty terminal
      exact ⟨ticks,.exhausted,run,by simp,by intro word impossible; cases impossible⟩
  | inr selected =>
      obtain ⟨parts,total,positive,hit,prefixTicks,tailTicks,source,last,prefixPath,empty,trace,tail,stable,accepted⟩ := selected
      have bounded : ∀ entry∈parts.map (fun j=>((),j)),entry.2≤n := by
        intro entry member
        obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
        exact (List.le_sum_of_mem inside).trans_eq total
      have halting : ∀ entry∈parts.map (fun j=>((),j)),
          (Hook.selectedSource M start entry.1).HaltingTransducer (generatorData entry.2) := by
        intro entry member
        exact OriginalSourceFamilySampler.selected_halting families (fun _ : Unit=>false) entry.1 entry.2
      obtain ⟨ticks,result,run,noReject⟩ := Hook.prefix_tail_halts C M parameter start ExpectedOriginalStarController.allowed
        (generatorData n) bits n (parts.map (fun j=>((),j))) bounded prefixTicks source last prefixPath empty trace stable halting _ accepted
      refine ⟨ticks,result,run,noReject,?_⟩
      intro word resultEqual
      have produced : ∃ time,(Hook.machine C M parameter start).run (generatorData n) bits time=.halted (.accepted word) :=
        ⟨ticks,by simpa only [resultEqual] using run⟩
      obtain ⟨records,calls,equal⟩ := (Hook.prefix_tail_accepted_iff C M parameter start ExpectedOriginalStarController.allowed
        (generatorData n) bits n (parts.map (fun j=>((),j))) bounded prefixTicks tailTicks source last prefixPath empty trace tail stable
        halting _ accepted word).mp produced
      rw [equal]
      apply OriginalSourceFamilySampler.starLayers_of_calls G bits source.randomHead n parts records positive total
      change Hook.SourceCalls (OriginalSourceFamilySampler.source (fun _=>G))
        (OriginalSourceFamilySampler.entry (fun _=>G) (fun _ : Unit=>false)) bits source.randomHead
        (parts.map (fun j=>((),j))) records at calls
      exact calls

theorem machine_halting (n : ℕ) : (machine G.machine p).HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨ticks,result,run,noReject,support⟩ := machine_total G p n bits
    exact ⟨ticks,result,run⟩
  · intro bits ticks rejected
    obtain ⟨time,result,run,noReject,support⟩ := machine_total G p n bits
    exact noReject ((machine G.machine p).halted_outcome_unique (generatorData n) bits time ticks _ _ run rejected)

theorem machine_language_subset (n : ℕ) :
    (machine G.machine p).generatedLanguage (generatorData n)⊆IndexedSupport.starLayers G.layer n := by
  intro word member
  obtain ⟨bits,ticks,produced⟩ := ((machine G.machine p).mem_generatedLanguage_iff_produces (generatorData n) word).mp member
  obtain ⟨time,result,run,noReject,support⟩ := machine_total G p n bits
  exact support word ((machine G.machine p).halted_outcome_unique (generatorData n) bits time ticks _ _ run produced)

end
end ComplexityOfGenerators.Simulation.OriginalStarGenerator
