import ComplexityOfGenerators.Simulation.CyclicGenerator.Program

/-! The word-at-a-time decider simulation inside the cyclic generator. The
candidate tape is read only during a decision. Source output is discarded, and
the touched-cell track records exactly the source's visited work interval. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

def wordTape (word : List α) (i : ℤ) : Symbol D :=
  {letter := if 0 ≤ i then word[i.toNat]? else none}

@[simp] theorem wordTape_nat (word : List α) (i : ℕ) :
    wordTape D word i = {letter := word[i]?} := by simp [wordTape]

def decisionConfig (word : List α) (seen : Bool) (random : ℕ) (source : Configuration D) : Config D where
  state := .execute source.state seen word[source.inputHead]?
  inputHead := 0
  auxiliaryHead := 0
  indexHead := word.length
  randomHead := random
  output := []
  head := fun j => if j = 0 then (source.inputHead : ℤ) else source.workHead
  tape := fun j i => if j = 0 then wordTape D word i
    else {work := source.work i, touched := decide (i ∈ source.visited)}

theorem decision_step (word : List α) (seen : Bool) (random : ℕ) (bits : BitString)
    (c : Configuration D) (headBound : c.inputHead ≤ word.length) (visited : c.workHead ∈ c.visited)
    (next : Fin D.states) (write : Option (Fin D.symbols)) (work input auxiliary index : Move)
    (emit : Option Unit)
    (action : D.transition c.state word[c.inputHead]? none none (c.work c.workHead) =
      .step next write work input auxiliary index emit) :
    (bank D).Steps (generatorData word.length) bits (decisionConfig D word seen random c) 4
      (decisionConfig D word seen random
        (D.stepConfiguration (decisionData word) c next write work input auxiliary index emit)) := by
  let B := bank D
  let c₀ := decisionConfig D word seen random c
  let newInput := input.onInput word.length c.inputHead
  let written : Symbol D := {
    work := match write with | none => c.work c.workHead | some a => some a
    touched := true}
  let c₁ := B.advance (generatorData word.length) c₀ (.moveInput next seen input)
    written work .stay .stay .stay none
  have first : B.Steps (generatorData word.length) bits c₀ 1 c₁ := by
    apply TransducerBank.TapeBank.Steps.single
    cases write <;> simp [B, c₀, TransducerBank.TapeBank.instruction, bank, decisionConfig,
      select, transition, action, written, visited]
  let inputMove := clampedReadMove (decide ((c.inputHead : ℤ) = 0))
    (decide (c.inputHead < word.length)) input
  have movedInput : inputMove.onInt c.inputHead = (newInput : ℤ) :=
    clampedReadMove_correct word.length c.inputHead headBound input
  have live : (word[c.inputHead]?).isSome = decide (c.inputHead < word.length) := by
    by_cases inside : c.inputHead < word.length
    · simp [List.getElem?_eq_getElem inside, inside]
    · simp [List.getElem?_eq_none (by omega : word.length ≤ c.inputHead), inside]
  let c₂ := B.advance (generatorData word.length) c₁ (.input next seen)
    (wordTape D word c.inputHead) inputMove .stay .stay .stay none
  have second : B.Steps (generatorData word.length) bits c₁ 1 c₂ := by
    apply TransducerBank.TapeBank.Steps.single
    simp [B, c₁, c₀, TransducerBank.TapeBank.instruction, TransducerBank.TapeBank.advance,
      bank, decisionConfig, select, transition, inputMove, live]
  let c₃ := B.advance (generatorData word.length) c₂ (.mark next seen word[newInput]?)
    (wordTape D word newInput) .stay .stay .stay .stay none
  have wordMemory : c₂.tape 0 = wordTape D word := by
    funext i
    change Function.update (wordTape D word) (c.inputHead : ℤ)
      (wordTape D word c.inputHead) i = wordTape D word i
    rw [Function.update_eq_self]
  have inputHead : c₂.head 0 = (newInput : ℤ) := by
    simpa [c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, bank, decisionConfig, select]
      using movedInput
  have third : B.Steps (generatorData word.length) bits c₂ 1 c₃ := by
    apply TransducerBank.TapeBank.Steps.single
    change TransducerBank.BankInstruction.step
      (Phase.mark next seen (c₂.tape 0 (c₂.head 0)).letter)
      (c₂.tape 0 (c₂.head 0)) .stay .stay .stay .stay none = _
    rw [wordMemory, inputHead, wordTape_nat]
  let c₄ := B.advance (generatorData word.length) c₃ (.execute next seen word[newInput]?)
    {c₃.tape 1 (c₃.head 1) with touched := true} .stay .stay .stay .stay none
  have fourth : B.Steps (generatorData word.length) bits c₃ 1 c₄ := by
    apply TransducerBank.TapeBank.Steps.single
    simp [TransducerBank.TapeBank.instruction, B, bank, c₃, select, transition,
      TransducerBank.TapeBank.advance]
  have same : c₄ = decisionConfig D word seen random
      (D.stepConfiguration (decisionData word) c next write work input auxiliary index emit) := by
    apply TransducerBank.BankConfiguration.ext
    · rfl
    · rfl
    · rfl
    · simp [c₄, c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, decisionConfig,
        Move.onInput, generatorData]
    · rfl
    · rfl
    · funext j
      fin_cases j
      · change c₂.head 0 = (newInput : ℤ)
        exact inputHead
      · simp [c₄, c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, bank, select,
          decisionConfig, Machine.stepConfiguration, Move.onInt]
    · have memory₃ : c₃.tape 0 = wordTape D word := by
        change Function.update (c₂.tape 0) (c₂.head 0) (wordTape D word newInput) = _
        rw [wordMemory, inputHead, Function.update_eq_self]
      have work₃ : c₃.tape 1 = Function.update
          (fun i => ({work := c.work i, touched := decide (i ∈ c.visited)} : Symbol D))
          c.workHead written := by
        simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, bank, select, decisionConfig]
      have workHead₃ : c₃.head 1 = work.onInt c.workHead := by
        simp [c₃, c₂, c₁, c₀, TransducerBank.TapeBank.advance, B, bank, select, decisionConfig]
      funext j i
      fin_cases j
      · simpa [c₄, TransducerBank.TapeBank.advance, B, bank, select, c₃, decisionConfig]
          using congrFun memory₃ i
      · change Function.update (c₃.tape 1) (c₃.head 1)
          {c₃.tape 1 (c₃.head 1) with touched := true} i = _
        rw [work₃, workHead₃]
        by_cases atNew : i = work.onInt c.workHead <;>
          by_cases atOld : i = c.workHead <;> cases write <;>
          simp [decisionConfig, Machine.stepConfiguration, written,
            Function.update_apply, atNew, atOld]
        all_goals subst i; simp_all only [visited, decide_true, Cell.mk.injEq, and_self, ite_true, ite_false, decide_false, Bool.or_true, and_true, eq_self]
  rw [← same]
  exact ((first.trans B second).trans B third).trans B fourth

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
