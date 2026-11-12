import ComplexityOfGenerators.Simulation.FixedFallbackBank

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit) (fallback : List α)

theorem fixedFallback_emit (n : ℕ) (bits : BitString) (word : List α) (remaining k : ℕ)
    (length : word.length = k + remaining) (c : FixedFallbackConfiguration S M fallback)
    (state : c.state = .emit) (head : c.head 2 = k)
    (tape : c.tape 2 = compositionCertificate S (auxiliaryDecision M) word)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0) (index : c.indexHead ≤ n) :
    (fixedFallbackBank S M fallback).Executes (generatorData n) bits c remaining
      (.accepted (c.output ++ (word.drop k))) := by
  let B := fixedFallbackBank S M fallback
  induction remaining generalizing k c with
  | zero =>
      have equal : k = word.length := by omega
      rw [equal, List.drop_length, List.append_nil]
      apply TransducerBank.TapeBank.Executes.accept
      simp [TransducerBank.TapeBank.instruction, fixedFallbackBank, fixedFallbackTransition, fixedFallbackSelect,
        state, tape, head, equal]
  | succ remaining ih =>
      have inside : k < word.length := by omega
      let letter := word[k]
      have lookup : word[k]? = some letter := List.getElem?_eq_getElem inside
      let cell := compositionCertificate S (auxiliaryDecision M) word k
      let d := B.advance (generatorData n) c (.emit) cell .right .stay .stay .stay
        (some letter)
      have table : B.instruction (generatorData n) c = .step (.emit) cell .right .stay .stay .stay
          (some letter) := by
        simp [B, TransducerBank.TapeBank.instruction, fixedFallbackBank, fixedFallbackTransition, fixedFallbackSelect,
          state, tape, head, cell, lookup]
      have state' : d.state = .emit := rfl
      have head' : d.head 2 = ((k + 1 : ℕ) : ℤ) := by
        simp [d, B, TransducerBank.TapeBank.advance, fixedFallbackBank, fixedFallbackSelect, state, head, Move.onInt]
      have tape' : d.tape 2 = c.tape 2 := by
        simp only [d, B, TransducerBank.TapeBank.advance, fixedFallbackBank, fixedFallbackSelect, state,
          Function.update_self, head]
        rw [show cell = c.tape 2 k by rw [tape], Function.update_eq_self]
      have input' : d.inputHead = 0 := by simp [d, TransducerBank.TapeBank.advance, Move.onInput, generatorData]
      have auxiliary' : d.auxiliaryHead = 0 := by simp [d, TransducerBank.TapeBank.advance, Move.onInput, generatorData]
      have index' : d.indexHead ≤ n := by simp [d, TransducerBank.TapeBank.advance, Move.onInput, generatorData]
      have rest := ih (k + 1) (by omega) d state' head' (tape'.trans tape) input' auxiliary' index'
      have path := TransducerBank.TapeBank.Executes.step c (.emit) cell .right .stay .stay .stay
        (some letter) remaining _ table rest
      rw [List.drop_eq_getElem_cons inside]
      simpa only [d, TransducerBank.TapeBank.advance, Option.toList_some, List.append_assoc, List.singleton_append, letter] using path

theorem fixedFallback_reset_emit (n : ℕ) (bits : BitString) (word : List α) (k : ℕ)
    (c : FixedFallbackConfiguration S M fallback) (state : c.state = .reset) (head : c.head 2 = k)
    (tape : c.tape 2 = compositionCertificate S (auxiliaryDecision M) word)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0) (index : c.indexHead ≤ n) :
    (fixedFallbackBank S M fallback).Executes (generatorData n) bits c (k + 1 + word.length)
      (.accepted (c.output ++ word)) := by
  have rewind := TransducerBank.TapeBank.rewind_steps (fixedFallbackBank S M fallback) (generatorData n) bits
    (.reset) (.emit) 2 rfl (by intros; rfl) k c state head
    (by simp [input, generatorData]) (by simp [auxiliary, generatorData]) index
  have emit := fixedFallback_emit S M fallback n bits word word.length 0 (by omega)
    {c with state := .emit, head := Function.update c.head 2 0} rfl (by simp) tape input auxiliary index
  simpa using rewind.executes _ emit

theorem fixedFallback_constant (n : ℕ) (bits : BitString) (remaining k : ℕ)
    (length : fallback.length = k + remaining) (c : FixedFallbackConfiguration S M fallback)
    (state : c.state = .constant ⟨k, by omega⟩) :
    (fixedFallbackBank S M fallback).Executes (generatorData n) bits c remaining
      (.accepted (c.output ++ fallback.drop k)) := by
  let B := fixedFallbackBank S M fallback
  induction remaining generalizing k c with
  | zero =>
      have equal : k = fallback.length := by omega
      rw [equal, List.drop_length, List.append_nil]
      apply TransducerBank.TapeBank.Executes.accept
      simp [TransducerBank.TapeBank.instruction, fixedFallbackBank, fixedFallbackTransition,
        fixedFallbackSelect, state, equal]
  | succ remaining ih =>
      have inside : k < fallback.length := by omega
      let cell := c.tape 0 (c.head 0)
      let d := B.advance (generatorData n) c (.constant ⟨k + 1, by omega⟩) cell
        .stay .stay .stay .stay (some fallback[k])
      have table : B.instruction (generatorData n) c =
          .step (.constant ⟨k + 1, by omega⟩) cell .stay .stay .stay .stay (some fallback[k]) := by
        simp [B, TransducerBank.TapeBank.instruction, fixedFallbackBank, fixedFallbackTransition,
          fixedFallbackSelect, state, inside, cell]
      have rest := ih (k + 1) (by omega) d rfl
      have path := TransducerBank.TapeBank.Executes.step c (.constant ⟨k + 1, by omega⟩) cell
        .stay .stay .stay .stay (some fallback[k]) remaining _ table rest
      rw [List.drop_eq_getElem_cons inside]
      simpa only [d, TransducerBank.TapeBank.advance, Option.toList_some,
        List.append_assoc, List.singleton_append] using path

end
end ComplexityOfGenerators.Simulation
