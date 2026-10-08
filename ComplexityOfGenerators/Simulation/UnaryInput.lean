import ComplexityOfGenerators.Foundations.RandomTape

/-!
# Interchanging a unary ordinary input and the family index

This adapter changes the finite transition table and exchanges the two read-only
heads. It preserves every primitive transition, the random tape, the work tape,
and the output. In particular, a loader for `List Unit` can run directly on a
generator's physical unary index tape; no arithmetic on an unbounded index is
performed inside a machine instruction.
-/

namespace ComplexityOfGenerators.Simulation

variable {A O : Type} (M : Machine Unit A O)

def unarySwapInstruction : Instruction O M.states M.symbols → Instruction O M.states M.symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom no yes
  | .step next write work input auxiliary index emit =>
      .step next write work index auxiliary input emit

def unarySwapMachine : Machine Unit A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition := fun state input auxiliary index work =>
    unarySwapInstruction M (M.transition state (index.map fun _ => ()) auxiliary
      (input.map fun _ => true) work)

def unarySwapData (data : InputData Unit A) : InputData Unit A where
  input := List.replicate data.index ()
  auxiliary := data.auxiliary
  index := data.input.length

def unarySwapConfiguration (c : Configuration M) : Configuration (unarySwapMachine M) where
  state := c.state
  inputHead := c.indexHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.inputHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

def unarySwapResult : RunState M → RunState (unarySwapMachine M)
  | .running c => .running (unarySwapConfiguration M c)
  | .halted result => .halted result

private theorem unit_getElem? (word : List Unit) (i : ℕ) :
    word[i]? = if i < word.length then some () else none := by
  by_cases inside : i < word.length
  · simp [inside]
  · simp [inside]

private theorem unarySwap_symbols (data : InputData Unit A) (c : Configuration M) :
    (unarySwapMachine M).transition (unarySwapConfiguration M c).state
      (unarySwapData data).input[(unarySwapConfiguration M c).inputHead]?
      (unarySwapData data).auxiliary[(unarySwapConfiguration M c).auxiliaryHead]?
      (if (unarySwapConfiguration M c).indexHead < (unarySwapData data).index then some true else none)
      ((unarySwapConfiguration M c).work (unarySwapConfiguration M c).workHead) =
    unarySwapInstruction M (M.transition c.state data.input[c.inputHead]?
      data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead)) := by
  simp only [unarySwapMachine, unarySwapConfiguration, unarySwapData, unit_getElem?,
    List.length_replicate]
  by_cases hi : c.inputHead < data.input.length <;>
    by_cases hn : c.indexHead < data.index <;> simp [hi, hn]

theorem unarySwap_observe (data : InputData Unit A) (bits : BitString) (c : Configuration M) :
    (unarySwapMachine M).observe (unarySwapData data) bits (unarySwapConfiguration M c) =
      unarySwapResult M (M.observe data bits c) := by
  simp only [Machine.observe, unarySwap_symbols]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes =>
      by_cases available : c.randomHead < bits.length <;>
        simp [unarySwapInstruction, unarySwapConfiguration, unarySwapResult, available]
  | step next write work input auxiliary index emit => rfl

theorem unarySwap_next (data : InputData Unit A) (bits : BitString) (c : Configuration M) :
    (unarySwapMachine M).next (unarySwapData data) bits (unarySwapConfiguration M c) =
      unarySwapResult M (M.next data bits c) := by
  simp only [Machine.next, unarySwap_symbols]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes =>
      simp only [unarySwapInstruction, unarySwapConfiguration]
      cases bits[c.randomHead]? with
      | none => rfl
      | some bit => cases bit <;> rfl
  | step next write work input auxiliary index emit =>
      simp only [unarySwapInstruction, unarySwapConfiguration, unarySwapData, List.length_replicate]
      cases write <;> cases emit <;> rfl

/-- The swap has no runtime overhead, even on short random tapes. -/
theorem unarySwap_run (data : InputData Unit A) (bits : BitString) (t : ℕ) :
    (unarySwapMachine M).run (unarySwapData data) bits t = unarySwapResult M (M.run data bits t) := by
  induction t with
  | zero => exact unarySwap_observe M data bits M.initialConfiguration
  | succ t ih =>
      simp only [Machine.run, ih]
      cases M.run data bits t with
      | halted result => rfl
      | running c =>
          simp only [unarySwapResult, unarySwap_next]
          cases M.next data bits c with
          | halted result => rfl
          | running d => exact unarySwap_observe M data bits d

theorem unarySwap_timeBound (data : InputData Unit A) (t : ℕ) (bound : M.TimeBound data t) :
    (unarySwapMachine M).TimeBound (unarySwapData data) t := by
  intro bits
  obtain ⟨result, halted⟩ := bound bits
  exact ⟨result, by rw [unarySwap_run, halted]; rfl⟩

theorem unarySwap_produces_iff (data : InputData Unit A) (bits : BitString) (word : List O) :
    (unarySwapMachine M).Produces (unarySwapData data) bits word ↔ M.Produces data bits word := by
  unfold Machine.Produces
  constructor
  · rintro ⟨t, produced⟩
    rw [unarySwap_run] at produced
    refine ⟨t, ?_⟩
    cases execution : M.run data bits t with
    | running c => simp [execution, unarySwapResult] at produced
    | halted result => simpa [execution, unarySwapResult] using produced
  · rintro ⟨t, produced⟩
    exact ⟨t, by rw [unarySwap_run, produced]; rfl⟩

theorem unarySwap_deterministic (deterministic : M.Deterministic) :
    (unarySwapMachine M).Deterministic := by
  intro state input auxiliary index work
  have h := deterministic state (index.map fun _ => ()) auxiliary (input.map fun _ => true) work
  simp only [unarySwapMachine]
  cases action : M.transition state (index.map fun _ => ()) auxiliary (input.map fun _ => true) work <;>
    simp_all [unarySwapInstruction]

@[simp] theorem unarySwap_decisionData (n : ℕ) :
    unarySwapData (decisionData (List.replicate n ())) = generatorData n := by
  simp [unarySwapData, decisionData, generatorData]

end ComplexityOfGenerators.Simulation
