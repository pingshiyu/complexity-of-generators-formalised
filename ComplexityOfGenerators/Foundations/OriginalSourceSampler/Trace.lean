import ComplexityOfGenerators.Foundations.OriginalSourceSampler.Moments

/-! Identify the sampler record directly from any actual accepted source
path, including paths run with additional unused random bits. -/
namespace ComplexityOfGenerators.Machine.OriginalSource
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

theorem accepted_path_record {bits : BitString} {ticks : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration ticks finish) {word : List O}
    (terminal : M.observe data bits finish=.halted (.accepted word)) :
    M.MinimalAcceptedSeed data (bits.take finish.randomHead) ∧
      time M data (bits.take finish.randomHead)=ticks ∧
      output M data (bits.take finish.randomHead)=word := by
  have produces : M.Produces data bits word := by
    refine ⟨ticks,?_⟩
    rw [← runFrom_initial,path.runFrom M,terminal]
  obtain ⟨short,initial,minimal⟩ := M.exists_minimal_accepted_prefix data bits ⟨word,produces⟩
  obtain ⟨shortFinish,shortPath,shortTerminal,shortCursor⟩ := native_path M data minimal
  obtain ⟨suffix,whole⟩ := initial
  have extended : M.Steps data bits M.initialConfiguration (time M data short) shortFinish := by
    rw [← whole]
    exact shortPath.append M suffix
  have observed := M.observe_accepted_independent_bits (second := bits) shortTerminal
  have lower := extended.le_terminal M path terminal
  have upper := path.le_terminal M extended observed
  have sameTime : time M data short=ticks := le_antisymm lower upper
  rw [sameTime] at extended
  have sameFinish := extended.unique M path
  rw [sameFinish] at observed shortCursor
  have sameWord : output M data short=word :=
    Outcome.accepted.inj (RunState.halted.inj (observed.symm.trans terminal))
  have consumed : bits.take finish.randomHead=short := by
    rw [shortCursor,← whole]
    simp
  rw [consumed]
  exact ⟨minimal,sameTime,sameWord⟩

theorem seed_of_accepted_path {bits : BitString} {ticks : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration ticks finish) {word : List O}
    (terminal : M.observe data bits finish=.halted (.accepted word))
    {stream : BitStream} (member : stream∈cylinder bits) :
    seed M data stream=some (bits.take finish.randomHead) := by
  apply (seed_eq_some_iff M data stream _).mpr
  exact ⟨(accepted_path_record M data path terminal).1,
    cylinder_mono_prefix (List.take_prefix _ _) member⟩

theorem tail_of_accepted_path {bits : BitString} {ticks : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration ticks finish) {word : List O}
    (terminal : M.observe data bits finish=.halted (.accepted word))
    {stream : BitStream} (member : stream∈cylinder bits) :
    tail M data stream=(splitStream finish.randomHead stream).2 := by
  have selected := seed_of_accepted_path M data path terminal member
  rw [tail_of_seed M data selected,List.length_take,
    Nat.min_eq_left (path.randomHead_le_length M (by simp [initialConfiguration]))]

end
end ComplexityOfGenerators.Machine.OriginalSource
