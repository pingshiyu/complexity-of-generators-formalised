import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler.Sequence

/-! The sequential stream records give actual finite-tape source paths at
the exact cumulative offsets required by the native controller. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α)

def FiniteTrace (bits : BitString) (offset : ℕ) (record : Record) : Prop :=
  offset+coins record≤bits.length ∧ ∃ finish,
    (families record.1).machine.Steps (generatorData record.2.1) (bits.drop offset)
      (families record.1).machine.initialConfiguration (time families record) finish ∧
    (families record.1).machine.observe (generatorData record.2.1) (bits.drop offset) finish=
      .halted (.accepted (word families record)) ∧ finish.randomHead=coins record

theorem NativeTrace.coins_le_time {stream : BitStream} {record : Record}
    (trace : NativeTrace families stream record) : coins record≤time families record := by
  obtain ⟨bits,finish,_,_,path,_,cursor⟩ := trace
  have bound := path.randomHead_le_time (families record.1).machine
  simpa only [cursor,Machine.initialConfiguration,Nat.zero_add] using bound

private theorem prefix_of_cylinder_offset (stream : BitStream) (total offset : ℕ) (bits : BitString)
    (member : (fun i => stream (offset+i))∈cylinder bits) (enough : offset+bits.length≤total) :
    bits <+: (streamPrefix stream total).drop offset := by
  apply List.prefix_iff_eq_take.mpr
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,streamPrefix_length]
    omega
  · intro i before _
    have known := member ⟨i,before⟩
    change stream (offset+i)=bits[i] at known
    simpa only [List.getElem_take,List.getElem_drop,streamPrefix,List.getElem_ofFn] using known.symm

theorem NativeTrace.native_prefix (stream : BitStream) (total offset : ℕ) (record : Record)
    (trace : NativeTrace families (fun i => stream (offset+i)) record)
    (enough : offset+coins record≤total) : FiniteTrace families (streamPrefix stream total) offset record := by
  obtain ⟨bits,finish,selected,member,path,terminal,cursor⟩ := trace
  have length : bits.length=coins record := by simp only [coins,selected,Option.getD_some]
  obtain ⟨suffix,whole⟩ := prefix_of_cylinder_offset stream total offset bits member (by omega)
  refine ⟨by simpa only [streamPrefix_length] using enough,finish,?_,?_,cursor⟩
  · rw [← whole]
    exact path.append (families record.1).machine suffix
  · exact (families record.1).machine.observe_accepted_independent_bits terminal

def FiniteSequenceTrace (bits : BitString) (offset : ℕ) : List Request → List Record → Prop
  | [],[] => True
  | entry::requests,record::records =>
      request record=entry ∧ FiniteTrace families bits offset record ∧
        FiniteSequenceTrace bits (offset+coins record) requests records
  | _,_ => False

theorem StreamTrace.native_prefix (stream : BitStream) (total offset : ℕ)
    (requests : List Request) (records : List Record)
    (trace : StreamTrace families (fun i => stream (offset+i)) requests records)
    (enough : offset+consumed records≤total) :
    FiniteSequenceTrace families (streamPrefix stream total) offset requests records := by
  induction requests generalizing records offset with
  | nil => cases records <;> exact trace
  | cons entry requests ih =>
      cases records with
      | nil => exact False.elim trace
      | cons record records =>
          rcases trace with ⟨same,first,rest⟩
          have budget : offset+(coins record+consumed records)≤total := by
            simpa only [consumed,List.map_cons,List.sum_cons] using enough
          refine ⟨same,first.native_prefix families stream total offset record (by omega),?_⟩
          apply ih (offset+coins record) records
          · simpa only [Nat.add_assoc] using rest
          · omega

theorem StreamTrace.consumed_le_totalTime {stream : BitStream} {requests : List Request} {records : List Record}
    (trace : StreamTrace families stream requests records) : consumed records≤totalTime families records := by
  induction requests generalizing stream records with
  | nil => cases records <;> simp_all [StreamTrace,consumed,totalTime]
  | cons entry requests ih =>
      cases records with
      | nil => exact False.elim trace
      | cons record records =>
          have first := trace.2.1.coins_le_time families
          have rest := ih trace.2.2
          simp only [consumed,totalTime] at rest
          simp only [consumed,totalTime,List.map_cons,List.sum_cons]
          omega

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
