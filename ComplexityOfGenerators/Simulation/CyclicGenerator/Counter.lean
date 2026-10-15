import ComplexityOfGenerators.Simulation.CyclicGenerator.Entry

/-! The finite word counter. Carry propagation resets only the leading maximal
letters, so one increment uses at most the word length in tape instructions. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

structure CounterResult (α : Type) where
  word : List α
  position : ℕ
  overflow : Bool

variable {α : Type} [Fintype α]

def incrementWord (first : α) : List α → CounterResult α
  | [] => ⟨[], 0, true⟩
  | a :: tail => match nextLetter a with
      | some b => ⟨b :: tail, 0, false⟩
      | none => let rest := incrementWord first tail
                ⟨first :: rest.word, rest.position + 1, rest.overflow⟩

theorem incrementWord_length (first : α) (word : List α) :
    (incrementWord first word).word.length = word.length := by
  induction word with
  | nil => rfl
  | cons a tail ih => cases lookup : nextLetter a <;> simp [incrementWord, lookup, ih]

theorem incrementWord_cost (first : α) (word : List α) :
    (incrementWord first word).position + (if (incrementWord first word).overflow then 0 else 1) ≤
      word.length := by
  induction word with
  | nil => simp [incrementWord]
  | cons a tail ih =>
      cases lookup : nextLetter a <;> simp [incrementWord, lookup]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_le_add_right ih 1

variable (D : Machine α Bool Unit)

theorem wordTape_set (word : List α) (i : ℕ) (inside : i < word.length) (a : α) :
    Function.update (wordTape D word) (i : ℤ) {letter := some a} = wordTape D (word.set i a) := by
  funext j
  cases j with
  | ofNat j =>
      by_cases same : j = i
      · subst j
        simp [inside]
      · have different : (j : ℤ) ≠ (i : ℤ) := by omega
        simp [Function.update_of_ne different, List.getElem?_set_ne (Ne.symm same)]
  | negSucc j =>
      have different : Int.negSucc j ≠ (i : ℤ) := by omega
      simp [Function.update_of_ne different, wordTape]

theorem wordTape_replace (front tail : List α) (a b : α) :
    Function.update (wordTape D (front ++ a :: tail)) (front.length : ℤ) {letter := some b} =
      wordTape D (front ++ b :: tail) := by
  simpa using wordTape_set D (front ++ a :: tail) front.length (by simp) b

theorem increment_steps (first : α) (least : firstLetter = some first)
    (suffix front : List α) (seen : Bool) (bits : BitString) (c : Config D)
    (state : c.state = .increment seen) (head : c.head 0 = front.length)
    (tape : c.tape 0 = wordTape D (front ++ suffix))
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0)
    (index : c.indexHead ≤ (front ++ suffix).length) :
    let result := incrementWord first suffix
    (bank D).Steps (generatorData (front ++ suffix).length) bits c
      (result.position + if result.overflow then 0 else 1)
      {c with
        state := if result.overflow then .increment seen else .wordStart seen
        head := Function.update c.head 0 ((front.length + result.position : ℕ) : ℤ)
        tape := Function.update c.tape 0 (wordTape D (front ++ result.word))} := by
  induction suffix generalizing front c with
  | nil =>
      have memory : wordTape D front = c.tape 0 := by simpa using tape.symm
      simpa [incrementWord, ← head, memory, ← state, Function.update_eq_self] using
        (TransducerBank.TapeBank.Steps.refl c (B := bank D)
          (data := generatorData front.length) (bits := bits))
  | cons a tail ih =>
      have index' : c.indexHead ≤ front.length + (tail.length + 1) := by simpa using index
      cases successor : nextLetter a with
      | some b =>
          have table : (bank D).instruction (generatorData (front ++ a :: tail).length) c =
              .step (.wordStart seen) {letter := some b} .stay .stay .stay .stay none := by
            simp [TransducerBank.TapeBank.instruction, bank, select, transition, state,
              head, tape, List.getElem?_append_right, successor]
          have step := TransducerBank.TapeBank.Steps.single (bank D) _ bits c _ _ _ _ _ _ _ table
          convert step using 1
          · simp [incrementWord, successor]
          apply TransducerBank.BankConfiguration.ext <;>
            simp [incrementWord, successor, TransducerBank.TapeBank.advance, bank, select,
              state, head, tape, wordTape_replace, input, auxiliary, generatorData,
              Move.onInput, Move.onInt, Nat.min_eq_left index']
      | none =>
          let d : Config D := {c with
            head := Function.update c.head 0 ((front.length + 1 : ℕ) : ℤ)
            tape := Function.update c.tape 0 (wordTape D (front ++ first :: tail))}
          have one : (bank D).Steps (generatorData (front ++ a :: tail).length) bits c 1 d := by
            have table : (bank D).instruction (generatorData (front ++ a :: tail).length) c =
                .step (.increment seen) {letter := some first} .right .stay .stay .stay none := by
              simp [TransducerBank.TapeBank.instruction, bank, select, transition, state,
                head, tape, List.getElem?_append_right, successor, least]
            have step := TransducerBank.TapeBank.Steps.single (bank D) _ bits c _ _ _ _ _ _ _ table
            convert step using 1
            apply TransducerBank.BankConfiguration.ext <;>
              simp [d, TransducerBank.TapeBank.advance, bank, select, state, head, tape,
                wordTape_replace, input, auxiliary, generatorData, Move.onInput, Move.onInt,
                Nat.min_eq_left index']
          have rest := ih (front ++ [first]) d state (by simp [d])
            (by simp [d, List.append_assoc]) input auxiliary (by simpa using index)
          have rest' : (bank D).Steps (generatorData (front ++ a :: tail).length) bits d
              ((incrementWord first tail).position + if (incrementWord first tail).overflow then 0 else 1)
              {d with
                state := if (incrementWord first tail).overflow then .increment seen else .wordStart seen
                head := Function.update d.head 0 ((front.length + 1 + (incrementWord first tail).position : ℕ) : ℤ)
                tape := Function.update d.tape 0 (wordTape D (front ++ first :: (incrementWord first tail).word))} := by
            simpa [List.append_assoc] using rest
          simpa [d, incrementWord, successor, Function.update_idem, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using one.trans (bank D) rest'

theorem increment_candidate (first : α) (least : firstLetter = some first)
    (word : List α) (seen : Bool) (random : ℕ) (bits : BitString) :
    let result := incrementWord first word
    (bank D).Steps (generatorData word.length) bits
      {candidateConfig D word seen random 0 with state := .increment seen}
      (result.position + if result.overflow then 0 else 1)
      {candidateConfig D result.word seen random result.position with
        state := if result.overflow then .increment seen else .wordStart seen} := by
  let c : Config D := {candidateConfig D word seen random 0 with state := .increment seen}
  have path := increment_steps D first least word [] seen bits c rfl
    (by simp [c, candidateConfig]) (by simp [c, candidateConfig]) rfl rfl (by simp [c, candidateConfig])
  dsimp only at path ⊢
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at path
  convert path using 1
  apply TransducerBank.BankConfiguration.ext
  all_goals simp [c, candidateConfig, incrementWord_length]
  · funext j
    fin_cases j <;> simp
  · funext j i
    fin_cases j <;> simp

theorem overflow_restart (word : List α) (random : ℕ) (bits : BitString) :
    (bank D).Steps (generatorData word.length) bits
      {candidateConfig D word true random word.length with state := .increment true} 1
      (candidateConfig D word false random word.length) := by
  apply TransducerBank.TapeBank.Steps.go
  · simp [candidateConfig, generatorData]
  · simp [candidateConfig, generatorData]
  · simp [candidateConfig, generatorData]
  · simp [TransducerBank.TapeBank.instruction, bank, select, transition, candidateConfig]

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
