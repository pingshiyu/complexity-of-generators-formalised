import ComplexityOfGenerators.Simulation.CyclicGenerator.Decision
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind

/-! Entry to a fresh decision. The word tape is retained and the source work
tape starts blank; the origin is marked before the first source instruction. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

def candidateConfig (word : List α) (seen : Bool) (random position : ℕ) : Config D where
  state := .wordStart seen
  inputHead := 0
  auxiliaryHead := 0
  indexHead := word.length
  randomHead := random
  output := []
  head := fun j => if j = 0 then (position : ℤ) else 0
  tape := fun j i => if j = 0 then wordTape D word i else {}

theorem candidate_entry (word : List α) (seen : Bool) (random position : ℕ) (bits : BitString) :
    (bank D).Steps (generatorData word.length) bits (candidateConfig D word seen random position)
      (position + 3) (decisionConfig D word seen random D.initialConfiguration) := by
  let c := candidateConfig D word seen random position
  let d : Config D := {c with state := .input D.initial seen, head := Function.update c.head 0 0}
  have rewind : (bank D).Steps (generatorData word.length) bits c (position + 1) d :=
    TransducerBank.TapeBank.rewind_steps (bank D) _ bits (.wordStart seen) (.input D.initial seen)
      0 rfl (by intros; rfl) position c rfl (by simp [c, candidateConfig])
      (by simp [c, candidateConfig, generatorData]) (by simp [c, candidateConfig, generatorData])
      (by simp [c, candidateConfig, generatorData])
  let e : Config D := {d with state := .mark D.initial seen word[0]?}
  have cache : (bank D).Steps (generatorData word.length) bits d 1 e := by
    apply TransducerBank.TapeBank.Steps.go
    · simp [d, c, candidateConfig, generatorData]
    · simp [d, c, candidateConfig, generatorData]
    · simp [d, c, candidateConfig, generatorData]
    · simp [TransducerBank.TapeBank.instruction, d, c, candidateConfig, bank, select, transition, wordTape]
  have mark : (bank D).Steps (generatorData word.length) bits e 1
      (decisionConfig D word seen random D.initialConfiguration) := by
    have table : (bank D).instruction (generatorData word.length) e =
        .step (.execute D.initial seen word[0]?) {touched := true}
          .stay .stay .stay .stay none := by
      simp [TransducerBank.TapeBank.instruction, e, d, c, candidateConfig, bank, select, transition, wordTape]
    have one := TransducerBank.TapeBank.Steps.single (bank D) _ bits e _ _ _ _ _ _ _ table
    convert one using 1
    apply TransducerBank.BankConfiguration.ext
    all_goals simp [TransducerBank.TapeBank.advance, decisionConfig, Machine.initialConfiguration,
      e, d, c, candidateConfig, bank, select, Move.onInput, Move.onInt, generatorData]
    · funext j
      fin_cases j <;> simp
    · funext j i
      fin_cases j <;> simp [Function.update_apply]
      by_cases zero : i = 0 <;> simp [zero]
  simpa [Nat.add_assoc] using (rewind.trans (bank D) cache).trans (bank D) mark

theorem wordTape_append (word : List α) (a : α) :
    Function.update (wordTape D word) (word.length : ℤ) {letter := some a} =
      wordTape D (word ++ [a]) := by
  funext i
  cases i with
  | ofNat i =>
      by_cases inside : i < word.length
      · have different : (i : ℤ) ≠ (word.length : ℤ) := by omega
        simp [Function.update_of_ne different, List.getElem?_append_left inside]
      · by_cases atEnd : i = word.length
        · simp [atEnd, List.getElem?_append_right]
        · have different : (i : ℤ) ≠ (word.length : ℤ) := by omega
          simp [Function.update_of_ne different,
            List.getElem?_eq_none (by omega : word.length ≤ i),
            List.getElem?_eq_none (by simp; omega : (word ++ [a]).length ≤ i)]
  | negSucc i =>
      have different : Int.negSucc i ≠ (word.length : ℤ) := by omega
      simp [Function.update_of_ne different, wordTape]

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
