import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler

/-! Finite lucky source witnesses use only their consumed random prefixes.
Concatenating these prefixes supplies genuine sequential calls at exact offsets,
including empty prefixes and zero-index source members. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α)

def MinimalRecord (record : Record) : Prop :=
  ∃ bits,record.2.2=some bits ∧
    (families record.1).machine.MinimalAcceptedSeed (generatorData record.2.1) bits

def seedWord (records : List Record) : BitString :=
  (records.map (fun record => record.2.2.getD [])).flatten

theorem seedWord_length (records : List Record) : (seedWord records).length=consumed records := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      simpa only [seedWord,List.map_cons,List.flatten_cons,List.length_append,consumed,
        List.sum_cons,coins] using congrArg (fun n => coins record+n) ih

theorem bounded_record (entry : Request) (bits : BitString) (ticks : ℕ) (output : List α)
    (run : (families entry.1).machine.run (generatorData entry.2) bits ticks=.halted (.accepted output)) :
    ∃ record,request record=entry ∧ MinimalRecord families record ∧
      word families record=output ∧ time families record≤ticks := by
  let M := (families entry.1).machine
  obtain ⟨elapsed,within,finish,path,observation⟩ := M.runFrom_path (generatorData entry.2) bits M.initialConfiguration ticks
  have terminal : M.observe (generatorData entry.2) bits finish=.halted (.accepted output) := by
    rw [Machine.runFrom_initial,run] at observation
    exact observation.symm
  obtain ⟨minimal,exactTime,exactWord⟩ := Machine.OriginalSource.accepted_path_record M (generatorData entry.2) path terminal
  exact ⟨(entry.1,entry.2,some (bits.take finish.randomHead)),rfl,
    ⟨_,rfl,minimal⟩,exactWord,exactTime.le.trans within⟩

theorem record_finiteTrace (record : Record) (minimal : MinimalRecord families record)
    (past future : BitString) :
    FiniteTrace families (past++record.2.2.getD []++future) past.length record := by
  obtain ⟨bits,selected,minimal⟩ := minimal
  obtain ⟨finish,path,terminal,cursor⟩ := Machine.OriginalSource.native_path
    (families record.1).machine (generatorData record.2.1) minimal
  have drop : (past++record.2.2.getD []++future).drop past.length=bits++future := by
    simp [selected,List.append_assoc]
  refine ⟨by simp [coins,List.length_append],finish,?_,?_,?_⟩
  · rw [drop]
    simpa only [time,selected] using path.append (families record.1).machine future
  · rw [drop]
    simpa only [word,selected] using
      (families record.1).machine.observe_accepted_independent_bits (second:=bits++future) terminal
  · simpa only [coins,selected,Option.getD_some] using cursor

theorem records_finiteTrace (records : List Record)
    (minimal : ∀ record∈records,MinimalRecord families record) (past future : BitString) :
    FiniteSequenceTrace families (past++seedWord records++future) past.length (records.map request) records := by
  induction records generalizing past with
  | nil => trivial
  | cons record records ih =>
      have first := record_finiteTrace families record (minimal record (by simp)) past (seedWord records++future)
      have rest := ih (fun r member => minimal r (by simp [member])) (past++record.2.2.getD [])
      refine ⟨rfl,?_,?_⟩
      · simpa only [seedWord,List.map_cons,List.flatten_cons,List.append_assoc] using first
      · simpa only [seedWord,List.map_cons,List.flatten_cons,List.append_assoc,List.length_append,coins] using rest

theorem FiniteSequenceTrace.length_eq {bits : BitString} {offset : ℕ}
    {requests : List Request} {records : List Record}
    (trace : FiniteSequenceTrace families bits offset requests records) : records.length=requests.length := by
  induction requests generalizing records offset with
  | nil => cases records <;> simp_all [FiniteSequenceTrace]
  | cons entry requests ih =>
      cases records with
      | nil => exact False.elim trace
      | cons record records => simpa only [List.length_cons] using congrArg (·+1) (ih trace.2.2)

def WordPath (clock : ℕ) (entry : Request) (output : List α) : Prop :=
  ∃ bits : BitString,(families entry.1).machine.run (generatorData entry.2) bits clock=.halted (.accepted output)

/-- All lucky calls can be realized on one finite random tape, with total
original runtime bounded by the number of factors times their common clock. -/
theorem bounded_records (clock : ℕ) (requests : List Request) (outputs : List (List α))
    (paths : List.Forall₂ (WordPath families clock) requests outputs) :
    ∃ records,records.map request=requests ∧ words families records=outputs.flatten ∧
      (∀ record∈records,MinimalRecord families record) ∧ totalTime families records≤requests.length*clock := by
  induction paths with
  | nil => exact ⟨[],rfl,rfl,by simp,by simp [totalTime]⟩
  | @cons entry output requests outputs path paths ih =>
      obtain ⟨bits,run⟩ := path
      obtain ⟨record,entryEqual,minimal,wordEqual,timeBound⟩ := bounded_record families entry bits clock output run
      obtain ⟨records,requestsEqual,wordsEqual,allMinimal,totalBound⟩ := ih
      refine ⟨record::records,by simp [entryEqual,requestsEqual],?_,?_,?_⟩
      · simp only [words,List.map_cons,List.flatten_cons,wordEqual]
        rw [show (records.map (word families)).flatten=outputs.flatten from wordsEqual]
      · intro r belongs
        rcases List.mem_cons.mp belongs with rfl|belongs
        · exact minimal
        · exact allMinimal r belongs
      · simp only [totalTime,List.map_cons,List.sum_cons,List.length_cons]
        change time families record+(records.map (time families)).sum≤_
        change (records.map (time families)).sum≤requests.length*clock at totalBound
        nlinarith

/-- Arbitrary supported factors also have a common finite execution tape; no
runtime bound is needed for this full-support witness. -/
theorem generated_records (requests : List Request) (outputs : List (List α))
    (members : List.Forall₂ (fun entry output => output∈(families entry.1).layer entry.2) requests outputs) :
    ∃ records,records.map request=requests ∧ words families records=outputs.flatten ∧
      ∀ record∈records,MinimalRecord families record := by
  induction members with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | @cons entry output requests outputs member members ih =>
      obtain ⟨bits,nonempty,ticks,run⟩ := member
      obtain ⟨record,entryEqual,minimal,wordEqual,_⟩ := bounded_record families entry bits ticks output run
      obtain ⟨records,requestsEqual,wordsEqual,allMinimal⟩ := ih
      refine ⟨record::records,by simp [entryEqual,requestsEqual],?_,?_⟩
      · simp only [words,List.map_cons,List.flatten_cons,wordEqual]
        rw [show (records.map (word families)).flatten=outputs.flatten from wordsEqual]
      · intro r belongs
        rcases List.mem_cons.mp belongs with rfl|belongs
        · exact minimal
        · exact allMinimal r belongs

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
