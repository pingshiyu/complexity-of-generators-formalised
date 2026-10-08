import ComplexityOfGenerators.Simulation.EvaluatorEncoding

/-!
# Primitive recursiveness of native bounded evaluation

The transition table has finite domain. All remaining operations are compositions
of Mathlib's primitive-recursive lookup, list, option, arithmetic and recursion
operations. In particular no computability hypothesis on the native evaluator
is introduced.
-/

namespace ComplexityOfGenerators.Simulation

variable {I A O : Type} [Primcodable I] [Primcodable A] [Primcodable O]
variable (M : Machine I A O)

theorem primrec_transition : Primrec (fun p : Fin M.states × Option I × Option A ×
    Option Bool × Option (Fin M.symbols) => M.transition p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
by
  let : Finite I := M.inputFinite
  let : Finite A := M.auxiliaryFinite
  let : Finite O := M.outputFinite
  exact Primrec.dom_finite _

theorem primrec_finiteInstruction : Primrec (fun p : InputData I A × FiniteConfiguration M =>
    finiteInstruction M p.1 p.2) := by
  have arguments : Primrec (fun p : InputData I A × FiniteConfiguration M =>
      (p.2.state, p.1.input[p.2.inputHead]?, p.1.auxiliary[p.2.auxiliaryHead]?,
        if p.2.indexHead < p.1.index then some true else none, p.2.work.lookup p.2.workHead)) := by
    apply Primrec.pair (primrec_config_state M |>.comp .snd)
    apply Primrec.pair
      (Primrec.list_getElem?.comp (primrec_data_input.comp .fst)
        (primrec_config_inputHead M |>.comp .snd))
    apply Primrec.pair
      (Primrec.list_getElem?.comp (primrec_data_auxiliary.comp .fst)
        (primrec_config_auxiliaryHead M |>.comp .snd))
    apply Primrec.pair
    · exact Primrec.ite
        (Primrec.nat_lt.comp (primrec_config_indexHead M |>.comp .snd) (primrec_data_index.comp .fst))
        (.const (some true)) (.const none)
    · exact Primrec.listLookup.comp (primrec_config_workHead M |>.comp .snd)
        (primrec_config_work M |>.comp .snd)
  exact (primrec_transition M).comp arguments

abbrev EvaluationInput := InputData I A × BitString × FiniteConfiguration M

theorem primrec_finiteObserve : Primrec (fun p : EvaluationInput M => finiteObserve M p.1 p.2.1 p.2.2) := by
  let hc : Primrec (fun p : EvaluationInput M => p.2.2) := Primrec.snd.comp .snd
  have instruction := (primrec_finiteInstruction M).comp (Primrec.fst.pair hc)
  have random : Primrec₂ (fun (p : EvaluationInput M) (_ : Fin M.states × Fin M.states) =>
      if p.2.2.randomHead < p.2.1.length then (Sum.inl p.2.2 : FiniteResult M)
      else Sum.inr (Sum.inr true)) :=
    (Primrec.ite
      (Primrec.nat_lt.comp
        (primrec_config_randomHead M |>.comp hc |>.comp .fst)
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd) |>.comp .fst))
      (Primrec.sumInl.comp (hc.comp .fst)) (.const (Sum.inr (Sum.inr true) : FiniteResult M))).to₂
  have step : Primrec₂ (fun (p : EvaluationInput M) (_ : StepCode O M.states M.symbols) =>
      (Sum.inl p.2.2 : FiniteResult M)) := (Primrec.sumInl.comp (hc.comp .fst)).to₂
  apply (primrec_instruction_cases instruction
    (Primrec.sumInr.comp (Primrec.sumInl.comp (primrec_config_output M |>.comp hc)))
    (.const (Sum.inr (Sum.inr false) : FiniteResult M)) random step).of_eq
  intro p
  unfold finiteObserve
  cases finiteInstruction M p.1 p.2.2 <;> rfl

def finiteStep (data : InputData I A) (c : FiniteConfiguration M)
    (step : StepCode O M.states M.symbols) : FiniteConfiguration M where
  state := step.1
  inputHead := step.2.2.2.1.onInput data.input.length c.inputHead
  auxiliaryHead := step.2.2.2.2.1.onInput data.auxiliary.length c.auxiliaryHead
  indexHead := step.2.2.2.2.2.1.onInput data.index c.indexHead
  randomHead := c.randomHead
  workHead := step.2.2.1.onInt c.workHead
  work := match step.2.1 with
    | none => c.work
    | some symbol => (c.workHead, symbol) :: c.work
  visited := step.2.2.1.onInt c.workHead :: c.visited
  output := match step.2.2.2.2.2.2 with
    | none => c.output
    | some symbol => c.output ++ [symbol]

theorem primrec_finiteStep : Primrec (fun p : InputData I A × FiniteConfiguration M ×
    StepCode O M.states M.symbols => finiteStep M p.1 p.2.1 p.2.2) := by
  let hc : Primrec (fun p : InputData I A × FiniteConfiguration M × StepCode O M.states M.symbols =>
      p.2.1) := Primrec.fst.comp .snd
  let hs : Primrec (fun p : InputData I A × FiniteConfiguration M × StepCode O M.states M.symbols =>
      p.2.2) := Primrec.snd.comp .snd
  let ht := Primrec.snd.comp hs
  let hm := Primrec.snd.comp ht
  let hi := Primrec.snd.comp hm
  let ha := Primrec.snd.comp hi
  let hn := Primrec.snd.comp ha
  let ho := Primrec.snd.comp hn
  let head := primrec_config_workHead M |>.comp hc
  let memory := primrec_config_work M |>.comp hc
  let output := primrec_config_output M |>.comp hc
  let moved := primrec_move_onInt.comp (Primrec.fst.comp hm) head
  unfold finiteStep
  apply primrec_configuration_mk M
  · exact Primrec.fst.comp hs
  · exact primrec_move_onInput.comp ((Primrec.fst.comp hi).pair
      ((Primrec.list_length.comp (primrec_data_input.comp .fst)).pair
        (primrec_config_inputHead M |>.comp hc)))
  · exact primrec_move_onInput.comp ((Primrec.fst.comp ha).pair
      ((Primrec.list_length.comp (primrec_data_auxiliary.comp .fst)).pair
        (primrec_config_auxiliaryHead M |>.comp hc)))
  · exact primrec_move_onInput.comp ((Primrec.fst.comp hn).pair
      ((primrec_data_index.comp .fst).pair (primrec_config_indexHead M |>.comp hc)))
  · exact primrec_config_randomHead M |>.comp hc
  · exact moved
  · exact Primrec.option_casesOn (Primrec.fst.comp ht) memory
      ((Primrec.list_cons.comp ((head.comp .fst).pair Primrec.snd)
        (memory.comp .fst)).to₂) |>.of_eq fun p => by cases p.2.2.2.1 <;> rfl
  · exact Primrec.list_cons.comp moved (primrec_config_visited M |>.comp hc)
  · exact Primrec.option_casesOn ho output
      ((Primrec.list_concat.comp (output.comp .fst) Primrec.snd).to₂) |>.of_eq
        fun p => by cases p.2.2.2.2.2.2.2.2 <;> rfl

theorem primrec_randomContinuation : Primrec (fun p : (EvaluationInput M × (Fin M.states × Fin M.states)) × Bool =>
    ({p.1.1.2.2 with
      state := if p.2 then p.1.2.2 else p.1.2.1
      randomHead := p.1.1.2.2.randomHead + 1} : FiniteConfiguration M)) := by
  let hc : Primrec (fun p : (EvaluationInput M × (Fin M.states × Fin M.states)) × Bool =>
      p.1.1.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst))
  apply primrec_configuration_mk M
  · have choice : Primrec (fun p : (EvaluationInput M × (Fin M.states × Fin M.states)) × Bool =>
        cond p.2 p.1.2.2 p.1.2.1) := Primrec.cond Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp .fst)) (Primrec.fst.comp (Primrec.snd.comp .fst))
    exact choice.of_eq fun p => by cases p.2 <;> rfl
  · exact primrec_config_inputHead M |>.comp hc
  · exact primrec_config_auxiliaryHead M |>.comp hc
  · exact primrec_config_indexHead M |>.comp hc
  · exact Primrec.succ.comp (primrec_config_randomHead M |>.comp hc)
  · exact primrec_config_workHead M |>.comp hc
  · exact primrec_config_work M |>.comp hc
  · exact primrec_config_visited M |>.comp hc
  · exact primrec_config_output M |>.comp hc

theorem primrec_finiteNext : Primrec (fun p : EvaluationInput M => finiteNext M p.1 p.2.1 p.2.2) := by
  let hc : Primrec (fun p : EvaluationInput M => p.2.2) := Primrec.snd.comp .snd
  have instruction := (primrec_finiteInstruction M).comp (Primrec.fst.pair hc)
  have random : Primrec₂ (fun (p : EvaluationInput M) (states : Fin M.states × Fin M.states) =>
      match p.2.1[p.2.2.randomHead]? with
      | none => (Sum.inr (Sum.inr true) : FiniteResult M)
      | some b => Sum.inl {p.2.2 with
          state := if b then states.2 else states.1
          randomHead := p.2.2.randomHead + 1}) := by
    have operation := Primrec.option_casesOn
      (Primrec.list_getElem?.comp ((Primrec.fst.comp Primrec.snd).comp .fst)
        (primrec_config_randomHead M |>.comp hc |>.comp .fst))
      (.const (Sum.inr (Sum.inr true) : FiniteResult M))
      ((Primrec.sumInl.comp (primrec_randomContinuation M)).to₂)
    exact operation.to₂.of_eq fun p states => by
      cases p.2.1[p.2.2.randomHead]? <;> rfl
  have step : Primrec₂ (fun (p : EvaluationInput M) (s : StepCode O M.states M.symbols) =>
      (Sum.inl (finiteStep M p.1 p.2.2 s) : FiniteResult M)) :=
    (Primrec.sumInl.comp ((primrec_finiteStep M).comp
      ((Primrec.fst.comp .fst).pair ((hc.comp .fst).pair Primrec.snd)))).to₂
  apply (primrec_instruction_cases instruction
    (Primrec.sumInr.comp (Primrec.sumInl.comp (primrec_config_output M |>.comp hc)))
    (.const (Sum.inr (Sum.inr false) : FiniteResult M)) random step).of_eq
  intro p
  unfold finiteNext
  cases finiteInstruction M p.1 p.2.2 <;> rfl

theorem primrec_finiteAdvance : Primrec (fun p : (InputData I A × BitString) × FiniteResult M =>
    match p.2 with
    | .inr result => Sum.inr result
    | .inl c => match finiteNext M p.1.1 p.1.2 c with
      | .inr result => Sum.inr result
      | .inl d => finiteObserve M p.1.1 p.1.2 d) := by
  have next : Primrec₂ (fun (p : (InputData I A × BitString) × FiniteResult M) c =>
      finiteNext M p.1.1 p.1.2 c) := ((primrec_finiteNext M).comp
    ((Primrec.fst.comp (Primrec.fst.comp .fst)).pair
      ((Primrec.snd.comp (Primrec.fst.comp .fst)).pair Primrec.snd))).to₂
  have continuation : Primrec₂ (fun (p : (InputData I A × BitString) × FiniteResult M) c =>
      match finiteNext M p.1.1 p.1.2 c with
      | .inr r => Sum.inr r
      | .inl d => finiteObserve M p.1.1 p.1.2 d) := by
    have core := Primrec.sumCasesOn next
      (((primrec_finiteObserve M).comp
        ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp .fst))).pair
          ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp .fst))).pair Primrec.snd))).to₂)
      (Primrec.sumInr.comp Primrec.snd).to₂
    exact core.to₂.of_eq fun p c => by
      cases h : finiteNext M p.1.1 p.1.2 c <;> simp [h]
  have advance := Primrec.sumCasesOn Primrec.snd continuation (Primrec.sumInr.comp Primrec.snd).to₂
  exact advance.of_eq fun p => by
    cases p.2 with
    | inr result => rfl
    | inl c => cases finiteNext M p.1.1 p.1.2 c <;> rfl

/-- Bounded evaluation is primitive recursive in all inputs, the finite random
tape, and the clock. Its operational correspondence is `finiteRun_denote`. -/
theorem primrec_finiteRun : Primrec (fun p : (InputData I A × BitString) × ℕ =>
    finiteRun M p.1.1 p.1.2 p.2) := by
  have initial : Primrec (fun p : InputData I A × BitString =>
      finiteObserve M p.1 p.2 (finiteInitial M)) := (primrec_finiteObserve M).comp
    (Primrec.fst.pair (Primrec.snd.pair (.const (finiteInitial M))))
  have successor : Primrec₂ (fun (p : InputData I A × BitString) (r : ℕ × FiniteResult M) =>
      match r.2 with
      | .inr result => Sum.inr result
      | .inl c => match finiteNext M p.1 p.2 c with
        | .inr result => Sum.inr result
        | .inl d => finiteObserve M p.1 p.2 d) := ((primrec_finiteAdvance M).comp
    (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to₂
  change Primrec₂ (fun (p : InputData I A × BitString) n => finiteRun M p.1 p.2 n)
  exact (Primrec.nat_rec initial successor).of_eq fun p n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [finiteRun, ← ih]; rfl

end ComplexityOfGenerators.Simulation
