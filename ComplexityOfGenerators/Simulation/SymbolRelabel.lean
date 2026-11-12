import ComplexityOfGenerators.Generators

/-! Native symbol relabelling preserves each transition and its time exactly. -/
namespace ComplexityOfGenerators.Simulation.SymbolRelabel
set_option backward.isDefEq.respectTransparency false
variable {I A O J B P : Type} [Fintype J] [Fintype B] [Fintype P]

def instruction {states symbols : ℕ} (output : O→P) :
    Instruction O states symbols→Instruction P states symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom no yes
  | .step q write work input aux index emit => .step q write work input aux index (emit.map output)

def machine (M : Machine I A O) (input : J→I) (auxiliary : B→A) (output : O→P) : Machine J B P where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition q i a n w := instruction output (M.transition q (i.map input) (a.map auxiliary) n w)

def data (input : J→I) (auxiliary : B→A) (d : InputData J B) : InputData I A :=
  ⟨d.input.map input,d.auxiliary.map auxiliary,d.index⟩

def configuration (M : Machine I A O) (input : J→I) (auxiliary : B→A) (output : O→P)
    (c : Configuration M) : Configuration (machine M input auxiliary output) where
  state := c.state
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output.map output

def outcome (output : O→P) : Outcome O→Outcome P
  | .accepted word => .accepted (word.map output)
  | .rejected => .rejected
  | .exhausted => .exhausted

def state (M : Machine I A O) (input : J→I) (auxiliary : B→A) (output : O→P) :
    RunState M→RunState (machine M input auxiliary output)
  | .running c => .running (configuration M input auxiliary output c)
  | .halted result => .halted (outcome output result)

variable (M : Machine I A O) (input : J→I) (auxiliary : B→A) (output : O→P)

@[simp] theorem initial : configuration M input auxiliary output M.initialConfiguration=
    (machine M input auxiliary output).initialConfiguration := rfl

theorem observe (d : InputData J B) (bits : BitString) (c : Configuration M) :
    (machine M input auxiliary output).observe d bits (configuration M input auxiliary output c)=
      state M input auxiliary output (M.observe (data input auxiliary d) bits c) := by
  simp only [Machine.observe,machine,configuration,data,List.getElem?_map]
  cases h : M.transition c.state (Option.map input d.input[c.inputHead]?)
    (Option.map auxiliary d.auxiliary[c.auxiliaryHead]?)
    (if c.indexHead<d.index then some () else none) (c.work c.workHead) <;>
    simp only [h,instruction,state,outcome] <;> first | rfl | (split_ifs <;> rfl)

theorem next (d : InputData J B) (bits : BitString) (c : Configuration M) :
    (machine M input auxiliary output).next d bits (configuration M input auxiliary output c)=
      state M input auxiliary output (M.next (data input auxiliary d) bits c) := by
  simp only [Machine.next,machine,configuration,data,List.getElem?_map,List.length_map]
  cases h : M.transition c.state (Option.map input d.input[c.inputHead]?)
    (Option.map auxiliary d.auxiliary[c.auxiliaryHead]?)
    (if c.indexHead<d.index then some () else none) (c.work c.workHead) with
  | accept => simp only [h,instruction,state,outcome] <;> first | rfl | (split_ifs <;> rfl)
  | reject => simp only [h,instruction,state,outcome] <;> first | rfl | (split_ifs <;> rfl)
  | readRandom no yes =>
      cases bit : bits[c.randomHead]? <;> simp only [h,instruction,bit,state,configuration,outcome] <;> rfl
  | step q write work i a n emit =>
      cases emit <;> simp only [h,instruction,state,configuration,Option.map,List.map_append,List.map_cons,List.map_nil] <;> congr 2 <;> cases write <;> funext z <;> simp

theorem run (d : InputData J B) (bits : BitString) (ticks : ℕ) :
    (machine M input auxiliary output).run d bits ticks=
      state M input auxiliary output (M.run (data input auxiliary d) bits ticks) := by
  induction ticks with
  | zero => simpa only [Machine.run,initial] using observe M input auxiliary output d bits M.initialConfiguration
  | succ ticks ih =>
      simp only [Machine.run,ih]
      cases r : M.run (data input auxiliary d) bits ticks with
      | halted result => rfl
      | running c =>
          simp only [state,next]
          cases s : M.next (data input auxiliary d) bits c with
          | halted result => rfl
          | running c' => exact observe M input auxiliary output d bits c'

theorem produces (d : InputData J B) (bits : BitString) (word : List P) :
    (machine M input auxiliary output).Produces d bits word ↔
      ∃ source,M.Produces (data input auxiliary d) bits source ∧ source.map output=word := by
  constructor
  · rintro ⟨ticks,accepted⟩
    rw [run] at accepted
    cases r : M.run (data input auxiliary d) bits ticks with
    | running c => simp [r,state] at accepted
    | halted result =>
        cases result with
        | rejected => simp [r,state,outcome] at accepted
        | exhausted => simp [r,state,outcome] at accepted
        | accepted value => exact ⟨value,⟨ticks,r⟩,by simpa [r,state,outcome] using accepted⟩
  · rintro ⟨source,⟨ticks,accepted⟩,rfl⟩
    exact ⟨ticks,by rw [run,accepted];rfl⟩

theorem accepts (d : InputData J B) (bits : BitString) :
    (machine M input auxiliary output).Accepts d bits ↔ M.Accepts (data input auxiliary d) bits := by
  constructor
  · rintro ⟨word,accepted⟩
    obtain ⟨source,accepted,equal⟩ := (produces M input auxiliary output d bits word).mp accepted
    exact ⟨source,accepted⟩
  · rintro ⟨source,accepted⟩
    exact ⟨source.map output,(produces M input auxiliary output d bits _).mpr ⟨source,accepted,rfl⟩⟩

theorem language (d : InputData J B) :
    (machine M input auxiliary output).generatedLanguage d=
      List.map output '' M.generatedLanguage (data input auxiliary d) := by
  ext word
  simp only [Machine.generatedLanguage,Set.mem_setOf_eq,Set.mem_image]
  constructor
  · rintro ⟨bits,nonempty,accepted⟩
    obtain ⟨source,accepted,equal⟩ := (produces M input auxiliary output d bits word).mp accepted
    exact ⟨source,⟨bits,nonempty,accepted⟩,equal⟩
  · rintro ⟨source,⟨bits,nonempty,accepted⟩,rfl⟩
    exact ⟨bits,nonempty,(produces M input auxiliary output d bits _).mpr ⟨source,accepted,rfl⟩⟩

theorem timeBound (d : InputData J B) (ticks : ℕ)
    (bound : M.TimeBound (data input auxiliary d) ticks) :
    (machine M input auxiliary output).TimeBound d ticks := by
  intro bits
  obtain ⟨result,accepted⟩ := bound bits
  exact ⟨outcome output result,by rw [run,accepted];rfl⟩

theorem halting (d : InputData J B) (source : M.HaltingTransducer (data input auxiliary d)) :
    (machine M input auxiliary output).HaltingTransducer d := by
  constructor
  · intro bits
    obtain ⟨ticks,result,accepted⟩ := source.1 bits
    exact ⟨ticks,outcome output result,by rw [run,accepted];rfl⟩
  · intro bits ticks rejected
    rw [run] at rejected
    cases r : M.run (data input auxiliary d) bits ticks with
    | running c => simp [r,state] at rejected
    | halted result =>
        cases result with
        | accepted value => simp [r,state,outcome] at rejected
        | exhausted => simp [r,state,outcome] at rejected
        | rejected => exact source.2 bits ticks r

theorem streams (d : InputData J B) :
    (machine M input auxiliary output).acceptedStreams d=M.acceptedStreams (data input auxiliary d) := by
  ext stream
  simp only [Machine.acceptedStreams,Set.mem_setOf_eq,accepts]

theorem generator (d : InputData J B) (source : M.IsGenerator (data input auxiliary d)) :
    (machine M input auxiliary output).IsGenerator d := by
  refine ⟨halting M input auxiliary output d source.1,?_⟩
  rw [streams]
  exact source.2

end ComplexityOfGenerators.Simulation.SymbolRelabel
