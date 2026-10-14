import ComplexityOfGenerators.Simulation.FallbackBank

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Unit) (bit allowEmpty : Bool)

def fallbackLetter (accepted bit letter : Bool) : Bool := if accepted then letter else bit

theorem fallback_emit (n : ℕ) (bits word : BitString) (accepted : Bool) (remaining k : ℕ)
    (length : word.length = k + remaining) (c : FallbackConfiguration M)
    (state : c.state = .emit accepted) (head : c.head 2 = k)
    (tape : c.tape 2 = compositionCertificate wordSampler (auxiliaryDecision M) word)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0) (index : c.indexHead ≤ n) :
    (fallbackBank M bit allowEmpty).Executes (generatorData n) bits c remaining
      (.accepted (c.output ++ (word.drop k).map (fallbackLetter accepted bit))) := by
  let B := fallbackBank M bit allowEmpty
  induction remaining generalizing k c with
  | zero =>
      have equal : k = word.length := by omega
      rw [equal, List.drop_length, List.map_nil, List.append_nil]
      apply TransducerBank.TapeBank.Executes.accept
      simp [TransducerBank.TapeBank.instruction, fallbackBank, fallbackTransition, fallbackSelect,
        state, tape, head, equal]
  | succ remaining ih =>
      have inside : k < word.length := by omega
      let letter := word[k]
      have lookup : word[k]? = some letter := List.getElem?_eq_getElem inside
      let cell := compositionCertificate wordSampler (auxiliaryDecision M) word k
      let d := B.advance (generatorData n) c (.emit accepted) cell .right .stay .stay .stay
        (some (fallbackLetter accepted bit letter))
      have table : B.instruction (generatorData n) c = .step (.emit accepted) cell .right .stay .stay .stay
          (some (fallbackLetter accepted bit letter)) := by
        simp [B, TransducerBank.TapeBank.instruction, fallbackBank, fallbackTransition, fallbackSelect,
          state, tape, head, cell, lookup, fallbackLetter]
      have state' : d.state = .emit accepted := rfl
      have head' : d.head 2 = ((k + 1 : ℕ) : ℤ) := by
        simp [d, B, TransducerBank.TapeBank.advance, fallbackBank, fallbackSelect, state, head, Move.onInt]
      have tape' : d.tape 2 = c.tape 2 := by
        simp only [d, B, TransducerBank.TapeBank.advance, fallbackBank, fallbackSelect, state,
          Function.update_self, head]
        rw [show cell = c.tape 2 k by rw [tape], Function.update_eq_self]
      have input' : d.inputHead = 0 := by simp [d, TransducerBank.TapeBank.advance, Move.onInput, generatorData]
      have auxiliary' : d.auxiliaryHead = 0 := by simp [d, TransducerBank.TapeBank.advance, Move.onInput, generatorData]
      have index' : d.indexHead ≤ n := by simp [d, TransducerBank.TapeBank.advance, Move.onInput, generatorData]
      have rest := ih (k + 1) (by omega) d state' head' (tape'.trans tape) input' auxiliary' index'
      have path := TransducerBank.TapeBank.Executes.step c (.emit accepted) cell .right .stay .stay .stay
        (some (fallbackLetter accepted bit letter)) remaining _ table rest
      rw [List.drop_eq_getElem_cons inside]
      simpa only [d, TransducerBank.TapeBank.advance, Option.toList_some, List.map_cons,
        List.append_assoc, List.singleton_append, letter] using path

theorem fallback_reset_emit (n : ℕ) (bits word : BitString) (accepted : Bool) (k : ℕ)
    (c : FallbackConfiguration M) (state : c.state = .reset accepted) (head : c.head 2 = k)
    (tape : c.tape 2 = compositionCertificate wordSampler (auxiliaryDecision M) word)
    (input : c.inputHead = 0) (auxiliary : c.auxiliaryHead = 0) (index : c.indexHead ≤ n) :
    (fallbackBank M bit allowEmpty).Executes (generatorData n) bits c (k + 1 + word.length)
      (.accepted (c.output ++ word.map (fallbackLetter accepted bit))) := by
  have rewind := TransducerBank.TapeBank.rewind_steps (fallbackBank M bit allowEmpty) (generatorData n) bits
    (.reset accepted) (.emit accepted) 2 rfl (by intros; rfl) k c state head
    (by simp [input, generatorData]) (by simp [auxiliary, generatorData]) index
  have emit := fallback_emit M bit allowEmpty n bits word accepted word.length 0 (by omega)
    {c with state := .emit accepted, head := Function.update c.head 2 0} rfl (by simp) tape input auxiliary index
  simpa using rewind.executes _ emit

end
end ComplexityOfGenerators.Simulation
