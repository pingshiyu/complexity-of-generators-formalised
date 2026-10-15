import ComplexityOfGenerators.Simulation.CyclicGenerator.Entry

/-! Copy the unary size into a word of least letters. The only stored word
has the requested length; the list of all candidates is never put on a tape. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

def loadConfig (a : α) (position : ℕ) : Config D where
  state := .load
  inputHead := 0
  auxiliaryHead := 0
  indexHead := position
  randomHead := 0
  output := []
  head := fun j => if j = 0 then (position : ℤ) else 0
  tape := fun j i => if j = 0 then wordTape D (List.replicate position a) i else {}

theorem load_step (a : α) (first : firstLetter = some a) (n position : ℕ)
    (inside : position < n) (bits : BitString) :
    (bank D).Steps (generatorData n) bits (loadConfig D a position) 1 (loadConfig D a (position + 1)) := by
  have table : (bank D).instruction (generatorData n) (loadConfig D a position) =
      .step .load {letter := some a} .right .stay .stay .right none := by
    simp [TransducerBank.TapeBank.instruction, bank, select, transition, loadConfig, generatorData,
      first, inside]
  have one := TransducerBank.TapeBank.Steps.single (bank D) _ bits _ _ _ _ _ _ _ _ table
  convert one using 1
  apply TransducerBank.BankConfiguration.ext
  all_goals simp [TransducerBank.TapeBank.advance, bank, select, loadConfig, generatorData,
    Move.onInput, Move.onInt, Nat.min_eq_left (by omega : position + 1 ≤ n)]
  · funext j
    fin_cases j <;> simp
  · funext j
    fin_cases j
    · change wordTape D (List.replicate (position + 1) a) = _
      rw [List.replicate_succ']
      simpa using (wordTape_append D (List.replicate position a) a).symm
    · simp

theorem load_steps (a : α) (first : firstLetter = some a) (n : ℕ) (bits : BitString)
    (position : ℕ) (bound : position ≤ n) :
    (bank D).Steps (generatorData n) bits (loadConfig D a position) (n - position + 1)
      (candidateConfig D (List.replicate n a) false 0 n) := by
  generalize remaining_eq : n - position = remaining
  induction remaining generalizing position with
  | zero =>
      have same : position = n := by omega
      subst position
      have go := TransducerBank.TapeBank.Steps.go (bank D) (generatorData n) bits (loadConfig D a n)
        (.wordStart false) (by simp [loadConfig, generatorData]) (by simp [loadConfig, generatorData])
        (by simp [loadConfig, generatorData]) (by
          simp [TransducerBank.TapeBank.instruction, bank, select, transition, loadConfig, generatorData])
      simpa [loadConfig, candidateConfig] using go
  | succ remaining ih =>
      have step := load_step D a first n position (by omega) bits
      have tail := ih (position + 1) (by omega) (by omega)
      simpa [Nat.add_comm, Nat.add_assoc] using step.trans (bank D) tail

theorem load_initial (a : α) (first : firstLetter = some a) (n : ℕ) (bits : BitString) :
    (bank D).Steps (generatorData n) bits (bank D).initialConfiguration (n + 1)
      (candidateConfig D (List.replicate n a) false 0 n) := by
  have blank : loadConfig D a 0 = (bank D).initialConfiguration := by
    apply TransducerBank.BankConfiguration.ext
    all_goals simp [loadConfig, TransducerBank.TapeBank.initialConfiguration, bank]
    funext j i
    simp [wordTape]
  simpa [blank] using load_steps D a first n bits 0 (Nat.zero_le _)

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
