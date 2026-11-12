import ComplexityOfGenerators.Foundations.OriginalSourceSampler.Seeds

/-! Native output, first accepting time and exact consumed cursor of the
source sampler. Its recorded cost is the original primitive runtime, not a
bounded or reweighted replacement distribution. -/
namespace ComplexityOfGenerators.Machine.OriginalSource
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

def output (bits : BitString) : List O := by
  classical
  exact if accepted : M.Accepts data bits then Classical.choose accepted else []

theorem produces_output {bits : BitString} (accepted : M.Accepts data bits) :
    M.Produces data bits (output M data bits) := by
  classical
  simpa only [output,dite_eq_left accepted] using Classical.choose_spec accepted

def time (bits : BitString) : ℕ := by
  classical
  exact if accepted : M.Produces data bits (output M data bits) then Nat.find accepted else 0

theorem run_time {bits : BitString} (accepted : M.Accepts data bits) :
    M.run data bits (time M data bits)=.halted (.accepted (output M data bits)) := by
  classical
  have produced := produces_output M data accepted
  simpa only [time,dite_eq_left produced] using Nat.find_spec produced

theorem time_minimal {bits : BitString} (accepted : M.Accepts data bits)
    {earlier : ℕ} (before : earlier<time M data bits) :
    M.run data bits earlier≠.halted (.accepted (output M data bits)) := by
  classical
  have produced := produces_output M data accepted
  have smaller : earlier<Nat.find produced := by simpa only [time,dite_eq_left produced] using before
  exact Nat.find_min produced smaller

theorem native_path {bits : BitString} (minimal : M.MinimalAcceptedSeed data bits) :
    ∃ finish, M.Steps data bits M.initialConfiguration (time M data bits) finish ∧
      M.observe data bits finish=.halted (.accepted (output M data bits)) ∧
      finish.randomHead=bits.length := by
  have run := run_time M data minimal.1
  obtain ⟨ticks,bound,finish,path,equal⟩ := M.runFrom_path data bits M.initialConfiguration (time M data bits)
  rw [runFrom_initial,run] at equal
  have terminal := equal.symm
  have exactTime : ticks=time M data bits := by
    apply le_antisymm bound
    by_contra smaller
    have first := time_minimal M data minimal.1 (by omega : ticks<time M data bits)
    have earlier := path.runFrom M
    rw [runFrom_initial,terminal] at earlier
    exact first earlier
  subst ticks
  exact ⟨finish,path,terminal,minimal.randomHead_eq M path terminal⟩

private theorem never_exhausted {bits : BitString} (accepted : M.Accepts data bits) (ticks : ℕ) :
    M.run data bits ticks≠.halted .exhausted := by
  obtain ⟨word,deadline,run⟩ := accepted
  intro exhausted
  have impossible := M.halted_outcome_unique data bits ticks deadline .exhausted (.accepted word) exhausted run
  cases impossible

/-- Every finite accepting prefix of the same stream has the same timed
behaviour on an accepting seed, even if it includes unused bits. -/
theorem run_of_streamAcceptsBy {bits : BitString} {stream : BitStream} {ticks : ℕ}
    (accepted : M.Accepts data bits) (member : stream∈cylinder bits)
    (byTime : M.streamAcceptsBy data stream ticks) :
    ∃ word, M.run data bits ticks=.halted (.accepted word) := by
  obtain ⟨other,word,otherMember,otherRun⟩ := byTime
  refine ⟨word,?_⟩
  rcases le_total bits.length other.length with short | short
  · obtain ⟨suffix,equal⟩ := cylinder_prefix_comparable member otherMember short
    rw [← equal,M.run_append_of_not_exhausted data bits suffix ticks (never_exhausted M data accepted ticks)] at otherRun
    exact otherRun
  · obtain ⟨suffix,equal⟩ := cylinder_prefix_comparable otherMember member short
    rw [← equal,M.run_append_of_not_exhausted data other suffix ticks (by simp [otherRun]),otherRun]

theorem output_eq {bits : BitString} {stream : BitStream}
    (accepted : M.Accepts data bits) (member : stream∈cylinder bits) :
    M.streamLength data stream=(output M data bits).length :=
  M.streamLength_of_produces data ⟨bits,member,produces_output M data accepted⟩

theorem runtime_eq {bits : BitString} {stream : BitStream}
    (accepted : M.Accepts data bits) (member : stream∈cylinder bits) :
    M.streamRuntime data stream=(time M data bits : ℝ≥0∞) := by
  apply M.streamRuntime_eq_of_first_acceptsBy data
    ⟨bits,output M data bits,member,run_time M data accepted⟩
  intro ticks before earlier
  obtain ⟨word,run⟩ := run_of_streamAcceptsBy M data accepted member earlier
  have same := M.produces_unique data bits word (output M data bits) ⟨ticks,run⟩
    (produces_output M data accepted)
  rw [same] at run
  exact time_minimal M data accepted before run

/-- The completed record is realised by the original native machine with
exactly this runtime and exactly this random-tape consumption. -/
theorem native_of_seed {stream : BitStream} {bits : BitString}
    (selected : seed M data stream=some bits) :
    stream∈cylinder bits ∧ ∃ finish,
      M.Steps data bits M.initialConfiguration (time M data bits) finish ∧
      M.observe data bits finish=.halted (.accepted (output M data bits)) ∧
      finish.randomHead=bits.length := by
  have ⟨minimal,member⟩ := (seed_eq_some_iff M data stream bits).mp selected
  exact ⟨member,native_path M data minimal⟩

def recordedLength (record : Option BitString) : ℝ≥0∞ :=
  match record with
  | none => 0
  | some bits => (output M data bits).length

def recordedTime (record : Option BitString) : ℝ≥0∞ :=
  match record with
  | none => 0
  | some bits => time M data bits

theorem recordedLength_eq {stream : BitStream} (accepted : stream∈M.acceptedStreams data) :
    recordedLength M data (seed M data stream)=(M.streamLength data stream : ℝ≥0∞) := by
  obtain ⟨bits,selected,member,minimal⟩ := seed_spec M data accepted
  rw [selected]
  change ((output M data bits).length : ℝ≥0∞)=_
  rw [output_eq M data minimal.1 member]

theorem recordedTime_eq {stream : BitStream} (accepted : stream∈M.acceptedStreams data) :
    recordedTime M data (seed M data stream)=M.streamRuntime data stream := by
  obtain ⟨bits,selected,member,minimal⟩ := seed_spec M data accepted
  rw [selected]
  change (time M data bits : ℝ≥0∞)=_
  exact (runtime_eq M data minimal.1 member).symm

end
end ComplexityOfGenerators.Machine.OriginalSource
