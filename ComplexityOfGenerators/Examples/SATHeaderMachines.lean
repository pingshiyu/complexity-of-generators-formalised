import ComplexityOfGenerators.Examples.SATHeader
import ComplexityOfGenerators.Foundations.ExecutionBounds

/-! Native finite-control transducers for the SAT header rank and width.
The work head stays fixed and every execution counts primitive transitions. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

/-- State 0 skips the unary capacity; state 1 emits the unary active count.
With `single`, state 2 accepts after the first emitted mark instead. -/
def headerMachine (single : Bool) : Machine Symbol Unit Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 3
  symbols := 0
  initial := 0
  transition := fun state input _ _ _ =>
    if state = 0 then
      .step (if input = some .one then 0 else 1) none .stay .right .stay .stay none
    else if state = 1 ∧ input = some .one then
      .step (if single then 2 else 1) none .stay .right .stay .stay (some ())
    else .accept

local instance (single : Bool) : NeZero (headerMachine single).states := ⟨by change 3 ≠ 0; decide⟩

theorem headerMachine_deterministic (single : Bool) : (headerMachine single).Deterministic := by
  intro state input auxiliary index work
  by_cases zero : state = 0
  · simp [headerMachine, zero]
  · by_cases flags : state = 1 ∧ input = some .one <;> simp [headerMachine, zero, flags]

def emittedCount (single : Bool) (count : ℕ) : ℕ := if single then min count 1 else count

private theorem drop_after_right {A : Type} (word : List A) (head : ℕ) :
    word.drop (Move.right.onInput word.length head) = (word.drop head).tail := by
  simp only [Move.onInput, List.tail_drop]
  by_cases bound : head + 1 ≤ word.length
  · rw [Nat.min_eq_left bound]
  · rw [Nat.min_eq_right (by omega)]
    simp [List.drop_eq_nil_iff.mpr (by omega : word.length ≤ head + 1)]

private theorem head_of_drop (data : InputData Symbol Unit) (head : ℕ) (word : List Symbol)
    (suffix : data.input.drop head = word) : data.input[head]? = word.head? := by
  have lookup := congrArg (fun xs : List Symbol => xs[0]?) suffix
  simpa [List.getElem?_drop, List.head?_eq_getElem?] using lookup

private theorem headerMachine_flags (single : Bool) (data : InputData Symbol Unit)
    (bits : BitString) (word : List Symbol) (c : Configuration (headerMachine single))
    (state : c.state = 1) (suffix : data.input.drop c.inputHead = word) :
    (headerMachine single).runFrom data bits c (emittedCount single (readOnes word).1) =
      .halted (.accepted (c.output ++ List.replicate (emittedCount single (readOnes word).1) ())) := by
  induction word generalizing c with
  | nil =>
    have head := head_of_drop data c.inputHead [] suffix
    simp [Machine.runFrom, Machine.observe, headerMachine, state, head, readOnes, emittedCount]
  | cons s rest ih =>
    have head := head_of_drop data c.inputHead (s :: rest) suffix
    by_cases one : s = .one
    · subst s
      let d := (headerMachine single).stepConfiguration data c
        (if single then 2 else 1) none .stay .right .stay .stay (some ())
      have instruction : (headerMachine single).transition c.state data.input[c.inputHead]?
          data.auxiliary[c.auxiliaryHead]? (if c.indexHead < data.index then some () else none)
          (c.work c.workHead) =
          .step (if single then 2 else 1) none .stay .right .stay .stay (some ()) := by
        simp [headerMachine, state, head]
      have live := (headerMachine single).observe_step data bits c _ _ _ _ _ _ _ instruction
      have step := (headerMachine single).next_step data bits c _ _ _ _ _ _ _ instruction
      have dropped : data.input.drop d.inputHead = rest := by
        change data.input.drop (Move.right.onInput data.input.length c.inputHead) = rest
        rw [drop_after_right, suffix]
        rfl
      cases single with
      | false =>
        have run := ih d rfl dropped
        have shifted := (headerMachine false).runFrom_shift data bits c d live step
          (emittedCount false (readOnes rest).1)
        simpa [emittedCount, readOnes, d, Machine.stepConfiguration,
          List.replicate_succ, List.append_assoc] using shifted.trans run
      | true =>
        have terminal : (headerMachine true).observe data bits d = .halted (.accepted d.output) := by
          simp [Machine.observe, headerMachine, d, Machine.stepConfiguration]
        have shifted := (headerMachine true).runFrom_shift data bits c d live step 0
        simpa [emittedCount, readOnes, d, Machine.stepConfiguration] using shifted.trans terminal
    · have other : readOnes (s :: rest) = (0, s :: rest) := by cases s <;> simp_all [readOnes]
      simp [Machine.runFrom, Machine.observe, headerMachine, state, head, one, other, emittedCount]

private theorem headerMachine_capacity (single : Bool) (data : InputData Symbol Unit)
    (bits : BitString) (word : List Symbol) (c : Configuration (headerMachine single))
    (state : c.state = 0) (suffix : data.input.drop c.inputHead = word) :
    (headerMachine single).runFrom data bits c
      ((readOnes word).1 + 1 + emittedCount single (headerRank word)) =
      .halted (.accepted (c.output ++ List.replicate (emittedCount single (headerRank word)) ())) := by
  induction word generalizing c with
  | nil =>
    have head := head_of_drop data c.inputHead [] suffix
    let d := (headerMachine single).stepConfiguration data c 1 none .stay .right .stay .stay none
    have instruction : (headerMachine single).transition c.state data.input[c.inputHead]?
        data.auxiliary[c.auxiliaryHead]? (if c.indexHead < data.index then some () else none)
        (c.work c.workHead) = .step 1 none .stay .right .stay .stay none := by
      simp [headerMachine, state, head]
    have live := (headerMachine single).observe_step data bits c _ _ _ _ _ _ _ instruction
    have step := (headerMachine single).next_step data bits c _ _ _ _ _ _ _ instruction
    have dropped : data.input.drop d.inputHead = [] := by
      change data.input.drop (Move.right.onInput data.input.length c.inputHead) = []
      rw [drop_after_right, suffix]
      rfl
    have run := headerMachine_flags single data bits [] d rfl dropped
    simp only [readOnes, emittedCount, Nat.zero_min, ite_self] at run
    have shifted := (headerMachine single).runFrom_shift data bits c d live step 0
    simpa [headerRank, readOnes, emittedCount, d, Machine.stepConfiguration] using shifted.trans run
  | cons s rest ih =>
    have head := head_of_drop data c.inputHead (s :: rest) suffix
    let d := (headerMachine single).stepConfiguration data c
      (if s = .one then 0 else 1) none .stay .right .stay .stay none
    have instruction : (headerMachine single).transition c.state data.input[c.inputHead]?
        data.auxiliary[c.auxiliaryHead]? (if c.indexHead < data.index then some () else none)
        (c.work c.workHead) =
        .step (if s = .one then 0 else 1) none .stay .right .stay .stay none := by
      simp [headerMachine, state, head]
    have live := (headerMachine single).observe_step data bits c _ _ _ _ _ _ _ instruction
    have step := (headerMachine single).next_step data bits c _ _ _ _ _ _ _ instruction
    have dropped : data.input.drop d.inputHead = rest := by
      change data.input.drop (Move.right.onInput data.input.length c.inputHead) = rest
      rw [drop_after_right, suffix]
      rfl
    by_cases one : s = .one
    · subst s
      have ds : d.state = 0 := by simp [d, Machine.stepConfiguration]
      have run := ih d ds dropped
      have shifted := (headerMachine single).runFrom_shift data bits c d live step
        ((readOnes rest).1 + 1 + emittedCount single (headerRank rest))
      simpa [readOnes, headerRank, d, Machine.stepConfiguration, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using shifted.trans run
    · have other : readOnes (s :: rest) = (0, s :: rest) := by cases s <;> simp_all [readOnes]
      have ds : d.state = 1 := by simp [d, one, Machine.stepConfiguration]
      have run := headerMachine_flags single data bits rest d ds dropped
      have shifted := (headerMachine single).runFrom_shift data bits c d live step
        (emittedCount single (readOnes rest).1)
      simpa [headerRank, other, d, Machine.stepConfiguration, Nat.add_comm] using shifted.trans run

theorem headerMachine_run (single : Bool) (data : InputData Symbol Unit) (bits : BitString) :
    (headerMachine single).run data bits
      ((readOnes data.input).1 + 1 + emittedCount single (headerRank data.input)) =
      .halted (.accepted (List.replicate (emittedCount single (headerRank data.input)) ())) := by
  have run := headerMachine_capacity single data bits data.input (headerMachine single).initialConfiguration
    rfl (by simp [Machine.initialConfiguration])
  rw [Machine.runFrom_initial] at run
  simpa [Machine.initialConfiguration] using run

theorem headerMachine_ticks_le (single : Bool) (word : List Symbol) :
    (readOnes word).1 + 1 + emittedCount single (headerRank word) ≤ word.length + 1 := by
  have first := readOnes_lengths word
  have second := readOnes_lengths (readOnes word).2.tail
  have tail : (readOnes word).2.tail.length ≤ (readOnes word).2.length := by
    simp only [List.length_tail]
    omega
  have emitted : emittedCount single (headerRank word) ≤ headerRank word := by
    cases single <;> simp [emittedCount]
  unfold headerRank at emitted ⊢
  omega

theorem headerMachine_bounded_run (single : Bool) (data : InputData Symbol Unit) (bits : BitString) :
    (headerMachine single).run data bits (data.input.length + 1) =
      .halted (.accepted (List.replicate (emittedCount single (headerRank data.input)) ())) := by
  have run := headerMachine_run single data bits
  have bound := headerMachine_ticks_le single data.input
  have padded := (headerMachine single).run_halted_add data bits _ _ run
    (data.input.length + 1 - ((readOnes data.input).1 + 1 + emittedCount single (headerRank data.input)))
  simpa only [Nat.add_sub_of_le bound] using padded

theorem headerMachine_timeBound (single : Bool) (data : InputData Symbol Unit) :
    (headerMachine single).TimeBound data (data.input.length + 1) :=
  fun bits => ⟨_, headerMachine_bounded_run single data bits⟩

@[simp] theorem emittedCount_true (count : ℕ) : emittedCount true count = width count := by
  cases count <;> simp [emittedCount, width]

/-- A native polynomial machine witness for the full unary header-rank
function, with both input lengths charged as required by the API. -/
def headerRank_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => List.replicate (headerRank word) ()) where
  machine := headerMachine false
  deterministic := headerMachine_deterministic false
  time := ⟨1, 1, by omega⟩
  timeBound := by
    intro word auxiliary bits
    let data : InputData Symbol Unit := { input := word, auxiliary := auxiliary }
    have run := headerMachine_bounded_run false data bits
    have padded := (headerMachine false).run_halted_add data bits (word.length + 1) _ run auxiliary.length
    refine ⟨.accepted (List.replicate (headerRank word) ()), ?_⟩
    simpa [data, emittedCount, PolynomialBound.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using padded
  computes := by
    intro word auxiliary
    refine ⟨word.length + 1, ?_⟩
    simpa [emittedCount] using headerMachine_bounded_run false
      ({ input := word, auxiliary := auxiliary } : InputData Symbol Unit) []

/-- The same native finite control stops after the first active-variable
mark, computing the zero-or-one block width. -/
def headerWidth_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => List.replicate (headerWidth word) ()) where
  machine := headerMachine true
  deterministic := headerMachine_deterministic true
  time := ⟨1, 1, by omega⟩
  timeBound := by
    intro word auxiliary bits
    let data : InputData Symbol Unit := { input := word, auxiliary := auxiliary }
    have run := headerMachine_bounded_run true data bits
    have padded := (headerMachine true).run_halted_add data bits (word.length + 1) _ run auxiliary.length
    refine ⟨.accepted (List.replicate (headerWidth word) ()), ?_⟩
    simpa [data, headerWidth, PolynomialBound.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using padded
  computes := by
    intro word auxiliary
    refine ⟨word.length + 1, ?_⟩
    simpa [headerWidth] using headerMachine_bounded_run true
      ({ input := word, auxiliary := auxiliary } : InputData Symbol Unit) []

end ComplexityOfGenerators.Examples.PaddedCNF
