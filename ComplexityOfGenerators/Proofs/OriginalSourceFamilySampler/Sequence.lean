import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler.Basic

/-! Sequential original calls use one stream and advance by the actual
consumed prefixes, including calls that consume no random bits. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
open MeasureTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α)

def samplers (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) :
    List (FreshStreamSampler Record) :=
  requests.attach.map (fun entry => call families entry.1.1 entry.1.2 (active entry.1 entry.2))

def calls (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) :
    FreshStreamSampler (List Record) := FreshStreamSampler.sequenceList (samplers families requests active)

theorem calls_nil (active : ∀ entry∈([] : List Request),((families entry.1).layer entry.2).Nonempty)
    (stream : BitStream) : (calls families [] active).run stream=([],stream) := rfl

theorem calls_cons (entry : Request) (requests : List Request)
    (active : ∀ item∈entry::requests,((families item.1).layer item.2).Nonempty) (stream : BitStream) :
    (calls families (entry::requests) active).run stream=
      (let first := (call families entry.1 entry.2 (active entry (by simp))).run stream
       let remaining := (calls families requests (fun item member => active item (by simp [member]))).run first.2
       (first.1::remaining.1,remaining.2)) := by
  simp [calls,samplers,List.attach_cons,List.map_map,Function.comp_def,
    FreshStreamSampler.sequenceList_cons]

theorem calls_requests (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) (stream : BitStream) :
    (((calls families requests active).run stream).1.map request)=requests := by
  induction requests generalizing stream with
  | nil => rfl
  | cons entry requests ih =>
      rw [calls_cons]
      simp only [List.map_cons,call_request]
      rw [ih]

theorem calls_tail (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) (stream : BitStream) :
    ((calls families requests active).run stream).2=
      fun i => stream (consumed ((calls families requests active).run stream).1+i) := by
  induction requests generalizing stream with
  | nil => simp [calls_nil,consumed]
  | cons entry requests ih =>
      rw [calls_cons]
      rw [ih]
      simp only [call_tail,consumed,List.map_cons,List.sum_cons,Nat.add_assoc]

def StreamTrace (stream : BitStream) : List Request → List Record → Prop
  | [],[] => True
  | entry::requests,record::records =>
      request record=entry ∧ NativeTrace families stream record ∧
        StreamTrace (fun i => stream (coins record+i)) requests records
  | _,_ => False

theorem calls_trace_ae (requests : List Request)
    (active : ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty) :
    ∀ᵐ stream∂fairCoinMeasure,
      StreamTrace families stream requests ((calls families requests active).run stream).1 := by
  induction requests with
  | nil => simp [calls,samplers,StreamTrace]
  | cons entry requests ih =>
      let tailActive : ∀ item∈requests,((families item.1).layer item.2).Nonempty :=
        fun item member => active item (by simp [member])
      have remaining := (call families entry.1 entry.2 (active entry (by simp))).tail_ae (ih tailActive)
      filter_upwards [call_native_ae families entry.1 entry.2 (active entry (by simp)),remaining]
        with stream first rest
      rw [calls_cons]
      change _ ∧ NativeTrace families stream _ ∧ _
      refine ⟨rfl,first,?_⟩
      simpa only [call_tail] using rest

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
