import ComplexityOfGenerators.ComplexityClasses

/-! Relabel a read-only input alphabet without changing the native work tape,
clock, or visited-cell accounting. This permits a stack interpreter to use a
larger work alphabet than the language's input alphabet. -/

namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false

variable {I J A O : Type} [Finite I] (M : Machine J A O) (encode : I → J)

def mapInput : Machine I A O where
  inputFinite := inferInstance
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition q input auxiliary index work := M.transition q (input.map encode) auxiliary index work

def mappedData (data : InputData I A) : InputData J A :=
  ⟨data.input.map encode, data.auxiliary, data.index⟩

def mappedConfiguration (c : Configuration (M.mapInput encode)) : Configuration M :=
  ⟨c.state, c.inputHead, c.auxiliaryHead, c.indexHead, c.randomHead,
    c.workHead, c.work, c.visited, c.output⟩

def mappedRun : RunState (M.mapInput encode) → RunState M
  | .running c => .running (M.mappedConfiguration encode c)
  | .halted result => .halted result

@[simp] theorem mapped_initial :
    M.mappedConfiguration encode (M.mapInput encode).initialConfiguration = M.initialConfiguration := rfl

theorem mapped_observe (data : InputData I A) (bits : BitString) (c : Configuration (M.mapInput encode)) :
    M.mappedRun encode ((M.mapInput encode).observe data bits c) =
      M.observe (mappedData encode data) bits (M.mappedConfiguration encode c) := by
  simp only [observe, mapInput, mappedData, mappedConfiguration, List.getElem?_map]
  cases M.transition c.state (data.input[c.inputHead]?.map encode) data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead) <;>
    first | rfl | (split_ifs <;> rfl)

theorem mapped_next (data : InputData I A) (bits : BitString) (c : Configuration (M.mapInput encode)) :
    M.mappedRun encode ((M.mapInput encode).next data bits c) =
      M.next (mappedData encode data) bits (M.mappedConfiguration encode c) := by
  simp only [next, mapInput, mappedData, mappedConfiguration, List.getElem?_map, List.length_map]
  cases M.transition c.state (data.input[c.inputHead]?.map encode) data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | step next write work input auxiliary index emit => cases write <;> cases emit <;> rfl
  | readRandom => cases bits[c.randomHead]? <;> rfl

/-- Relabelling costs no extra transitions, including at halting observations. -/
theorem mapped_run (data : InputData I A) (bits : BitString) (ticks : ℕ) :
    M.mappedRun encode ((M.mapInput encode).run data bits ticks) =
      M.run (mappedData encode data) bits ticks := by
  induction ticks with
  | zero => simpa only [run, mapped_initial] using M.mapped_observe encode data bits (M.mapInput encode).initialConfiguration
  | succ ticks ih =>
      rw [run, run, ← ih]
      cases previous : (M.mapInput encode).run data bits ticks with
      | halted result => rfl
      | running c =>
          simp only [mappedRun]
          rw [← M.mapped_next encode data bits c]
          cases step : (M.mapInput encode).next data bits c with
          | halted result => rfl
          | running d => exact M.mapped_observe encode data bits d

theorem mapInput_run_halted_iff (data : InputData I A) (bits : BitString) (ticks : ℕ) (result : Outcome O) :
    (M.mapInput encode).run data bits ticks = .halted result ↔
      M.run (mappedData encode data) bits ticks = .halted result := by
  rw [← M.mapped_run encode]
  cases (M.mapInput encode).run data bits ticks <;> simp [mappedRun]

theorem mapInput_halts_iff (data : InputData I A) (bits : BitString) :
    (M.mapInput encode).Halts data bits ↔ M.Halts (mappedData encode data) bits := by
  simp only [Halts, HaltsWithin, mapInput_run_halted_iff]

theorem mapInput_accepts_iff (data : InputData I A) (bits : BitString) :
    (M.mapInput encode).Accepts data bits ↔ M.Accepts (mappedData encode data) bits := by
  simp only [Accepts, Produces, mapInput_run_halted_iff]

theorem mapInput_deterministic (deterministic : M.Deterministic) :
    (M.mapInput encode).Deterministic := by
  intro q input auxiliary index work
  have source := deterministic q (input.map encode) auxiliary index work
  dsimp only [mapInput]
  cases action : M.transition q (input.map encode) auxiliary index work <;>
    simp_all only [action, Deterministic]

/-- In particular, the terminal successor's visited set is preserved. -/
theorem mapInput_spaceBound (data : InputData I A) (space : ℕ)
    (bounded : M.SpaceBound (mappedData encode data) space) :
    (M.mapInput encode).SpaceBound data space := by
  refine ⟨bounded.1, ?_⟩
  intro bits ticks c running
  have source : M.run (mappedData encode data) bits ticks = .running (M.mappedConfiguration encode c) := by
    rw [← M.mapped_run encode, running]
    rfl
  obtain ⟨before, after⟩ := bounded.2 bits ticks _ source
  refine ⟨before, ?_⟩
  intro d next
  apply after (M.mappedConfiguration encode d)
  rw [← M.mapped_next encode, next]
  rfl

end ComplexityOfGenerators.Machine

namespace ComplexityOfGenerators

/-- Inverse images of letterwise input encodings preserve native PSPACE.
No injectivity assumption or alphabet-size charge is needed. -/
theorem pspace_preimage_map {I J : Type} [Fintype I] [Fintype J]
    (encode : I → J) {L : Language J} (member : L ∈ PSPACE J) :
    {word : Word I | word.map encode ∈ L} ∈ PSPACE I := by
  obtain ⟨M, p, deterministic, halts, bounded, correct⟩ := member
  refine ⟨M.mapInput encode, p, M.mapInput_deterministic encode deterministic, ?_, ?_, ?_⟩
  · intro word
    exact (M.mapInput_halts_iff encode _ _).mpr (halts (word.map encode))
  · intro word
    exact M.mapInput_spaceBound encode _ _ (by simpa [Machine.mappedData, decisionData] using bounded (word.map encode))
  · intro word
    exact (M.mapInput_accepts_iff encode _ _).trans (correct (word.map encode))

end ComplexityOfGenerators
