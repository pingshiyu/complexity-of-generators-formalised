import ComplexityOfGenerators.Proofs.PaperCertificateBounds

/-! Ignore an arbitrary read-only certificate tape when reusing a family
machine whose auxiliary tape is empty. All source transitions and outcomes are
preserved exactly; the unobserved physical auxiliary head is projected away. -/
namespace ComplexityOfGenerators.PaperCertificates.IgnoreAuxiliary
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} [Fintype A] (M : Machine I Bool O)

def machine : Machine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := inferInstance
  outputFinite := M.outputFinite
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition q input _ index work := M.transition q input none index work

def data (d : InputData I A) : InputData I Bool := {input:=d.input,index:=d.index}

def configuration (c : Configuration (machine (A:=A) M)) : Configuration M :=
  ⟨c.state,c.inputHead,0,c.indexHead,c.randomHead,c.workHead,c.work,c.visited,c.output⟩

def state : RunState (machine (A:=A) M)→RunState M
  | .running c => .running (configuration M c)
  | .halted result => .halted result

theorem observe (d : InputData I A) (bits : BitString) (c : Configuration (machine M)) :
    state M ((machine M).observe d bits c)=M.observe (data d) bits (configuration M c) := by
  simp only [Machine.observe,machine,data,configuration,List.getElem?_nil]
  cases M.transition c.state d.input[c.inputHead]? none
    (if c.indexHead<d.index then some () else none) (c.work c.workHead) <;>
    first | rfl | (split_ifs <;> rfl)

theorem next (d : InputData I A) (bits : BitString) (c : Configuration (machine M)) :
    state M ((machine M).next d bits c)=M.next (data d) bits (configuration M c) := by
  simp only [Machine.next,machine,data,configuration,List.getElem?_nil]
  cases M.transition c.state d.input[c.inputHead]? none
    (if c.indexHead<d.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes => cases bits[c.randomHead]? <;> rfl
  | step next write work input auxiliary index emit =>
      cases auxiliary <;> cases write <;> cases emit <;> rfl

theorem run (d : InputData I A) (bits : BitString) (ticks : ℕ) :
    state M ((machine M).run d bits ticks)=M.run (data d) bits ticks := by
  induction ticks with
  | zero => exact observe M d bits (machine M).initialConfiguration
  | succ ticks ih =>
      rw [Machine.run,Machine.run,←ih]
      cases previous : (machine M).run d bits ticks with
      | halted result => rfl
      | running c =>
          simp only [state]
          rw [←next M d bits c]
          cases step : (machine M).next d bits c with
          | halted result => rfl
          | running d' => exact observe M d bits d'

theorem run_halted_iff (d : InputData I A) (bits : BitString) (ticks : ℕ) (result : Outcome O) :
    (machine M).run d bits ticks=.halted result↔M.run (data d) bits ticks=.halted result := by
  rw [←run M d bits ticks]
  cases (machine M).run d bits ticks <;> simp [state]

theorem produces (d : InputData I A) (bits : BitString) (word : Word O) :
    (machine M).Produces d bits word↔M.Produces (data d) bits word := by
  simp only [Machine.Produces,run_halted_iff]

theorem language (d : InputData I A) :
    (machine M).generatedLanguage d=M.generatedLanguage (data d) := by
  ext word
  simp only [Machine.generatedLanguage,Set.mem_setOf_eq,produces]

theorem acceptingTimeBound (d : InputData I A) (ticks : ℕ)
    (bounded : M.AcceptingTimeBound (data d) ticks) :
    (machine M).AcceptingTimeBound d ticks := by
  intro bits word produced
  exact (run_halted_iff M d bits ticks _).mpr (bounded bits word ((produces M d bits word).mp produced))

theorem generator (d : InputData I A) (source : M.IsGenerator (data d)) :
    (machine M).IsGenerator d := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro bits
    obtain ⟨ticks,result,halted⟩ := source.1.1 bits
    exact ⟨ticks,result,(run_halted_iff M d bits ticks result).mpr halted⟩
  · intro bits ticks rejected
    exact source.1.2 bits ticks ((run_halted_iff M d bits ticks .rejected).mp rejected)
  · have streams : (machine M).acceptedStreams d=M.acceptedStreams (data d) := by
      ext stream
      simp only [Machine.acceptedStreams,Machine.Accepts,Set.mem_setOf_eq,produces]
    rw [streams]
    exact source.2

end ComplexityOfGenerators.PaperCertificates.IgnoreAuxiliary
