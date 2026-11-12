import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler
import ComplexityOfGenerators.Simulation.NativeChoice.Properties
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Records

/-! Actual sampler source paths enter the common native finite-choice table
without changing their primitive runtime, output or random-bit consumption. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α E : Type} [Fintype α] [Fintype E] (families : Bool → UniformGenerators α)
    (tag : E → Bool)

def source : Machine Unit Bool α := NativeChoice.machine (fun b=>(families b).machine) false

def entry (event : E) : Fin (source families).states :=
  NativeChoice.start (fun b=>(families b).machine) (tag event)

theorem selected_source (event : E) :
    NativeSourceCall.Hook.selectedSource (source families) (entry families tag) event=
      NativeChoice.machine (fun b=>(families b).machine) (tag event) :=
  NativeChoice.machine_with_initial (fun b=>(families b).machine) false (tag event)

def hookRecord (record : Record) : NativeSourceCall.Hook.CallRecord α :=
  ⟨word families record,time families record,coins record⟩

@[simp] theorem hookRecord_words (records : List Record) :
    NativeSourceCall.Hook.words (records.map (hookRecord families))=words families records := by
  simp only [NativeSourceCall.Hook.words,words,List.map_map,hookRecord,Function.comp_def]
@[simp] theorem hookRecord_time (records : List Record) :
    NativeSourceCall.Hook.totalTime (records.map (hookRecord families))=totalTime families records := by
  simp only [NativeSourceCall.Hook.totalTime,totalTime,List.map_map,hookRecord,Function.comp_def]
@[simp] theorem hookRecord_coins (records : List Record) :
    NativeSourceCall.Hook.totalCoins (records.map (hookRecord families))=consumed records := by
  simp only [NativeSourceCall.Hook.totalCoins,consumed,List.map_map,hookRecord,Function.comp_def]

theorem finiteTrace_hook (bits : BitString) (offset : ℕ) (record : Record) (event : E) (index : ℕ)
    (trace : FiniteTrace families bits offset record) (sourceTag : record.1=tag event)
    (sourceIndex : record.2.1=index) :
    NativeSourceCall.Hook.CallAt (source families) (entry families tag) bits offset event index
      (hookRecord families record) := by
  rcases record with ⟨recordTag,recordIndex,seed⟩
  change recordTag=tag event at sourceTag
  change recordIndex=index at sourceIndex
  subst recordTag
  subst recordIndex
  let record : Record := (tag event,index,seed)
  obtain ⟨_,finish,path,terminal,cursor⟩ := trace
  unfold NativeSourceCall.Hook.CallAt
  rw [selected_source families tag event]
  have path' := NativeChoice.steps (fun b=>(families b).machine) (tag event)
    (generatorData index) (bits.drop offset) path
  have terminal' := NativeChoice.observe (fun b=>(families b).machine) (tag event)
    (generatorData index) (bits.drop offset) finish
  rw [terminal] at terminal'
  refine ⟨NativeChoice.configuration (fun b=>(families b).machine) (tag event) finish,?_,?_,?_⟩
  · simpa only [NativeChoice.configuration_initial,hookRecord] using path'
  · simpa only [hookRecord,NativeChoice.runState] using terminal'
  · exact cursor

theorem finiteSequenceTrace_hook (bits : BitString) (offset : ℕ)
    (requests : List Request) (records : List Record) (events : List (E×ℕ))
    (trace : FiniteSequenceTrace families bits offset requests records)
    (compatible : events.map (fun event => (tag event.1,event.2))=requests) :
    NativeSourceCall.Hook.SourceCalls (source families) (entry families tag) bits offset events
      (records.map (hookRecord families)) := by
  induction events generalizing offset requests records with
  | nil =>
      have requestEmpty : requests=[] := by simpa using compatible.symm
      subst requests
      cases records <;> exact trace
  | cons event events ih =>
      cases requests with
      | nil => simp at compatible
      | cons request requests =>
          cases records with
          | nil => exact False.elim trace
          | cons record records =>
              rcases trace with ⟨same,first,rest⟩
              simp only [List.map_cons,List.cons.injEq] at compatible
              refine ⟨finiteTrace_hook families tag bits offset record event.1 event.2 first ?_ ?_,?_⟩
              · exact (congrArg Prod.fst same).trans (congrArg Prod.fst compatible.1.symm)
              · exact (congrArg Prod.snd same).trans (congrArg Prod.snd compatible.1.symm)
              · exact ih (offset+coins record) requests records rest compatible.2

theorem selected_halting (event : E) (index : ℕ) :
    (NativeSourceCall.Hook.selectedSource (source families) (entry families tag) event).HaltingTransducer
      (generatorData index) := by
  rw [selected_source]
  exact NativeChoice.halting (fun b=>(families b).machine) (tag event) (generatorData index)
    ((families (tag event)).isGenerator index).1

/-- A hooked source acceptance belongs to the original requested layer. -/
theorem callAt_member (bits : BitString) (offset : ℕ) (event : E) (index : ℕ)
    (record : NativeSourceCall.Hook.CallRecord α)
    (call : NativeSourceCall.Hook.CallAt (source families) (entry families tag) bits offset event index record) :
    record.word∈(families (tag event)).layer index := by
  unfold NativeSourceCall.Hook.CallAt at call
  rw [selected_source families tag event] at call
  obtain ⟨finish,path,terminal,_⟩ := call
  apply ((families (tag event)).machine.mem_generatedLanguage_iff_produces (generatorData index) record.word).mpr
  refine ⟨bits.drop offset,(NativeChoice.produces_iff (fun b=>(families b).machine)
    (tag event) (generatorData index) (bits.drop offset) record.word).mp ?_⟩
  refine ⟨record.time,?_⟩
  rw [←Machine.runFrom_initial,path.runFrom,terminal]

/-- Source-call records retain the original layer memberships factor by factor. -/
theorem sourceCalls_members {bits : BitString} {offset : ℕ} {events : List (E×ℕ)}
    {records : List (NativeSourceCall.Hook.CallRecord α)}
    (calls : NativeSourceCall.Hook.SourceCalls (source families) (entry families tag) bits offset events records) :
    List.Forall₂ (fun event record => record.word∈(families (tag event.1)).layer event.2) events records := by
  induction events generalizing records offset with
  | nil => cases records <;> simp_all [NativeSourceCall.Hook.SourceCalls]
  | cons event events ih =>
      cases records with
      | nil => exact False.elim calls
      | cons record records => exact .cons (callAt_member families tag bits offset event.1 event.2 record calls.1) (ih calls.2)

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
