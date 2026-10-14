import ComplexityOfGenerators.Simulation.SamplerComposition

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

abbrev CompositionConfiguration :=
  TransducerBank.BankConfiguration α (CompositionState S R) (CompositionSymbol S R) 4

def compositionCertificate (word : BitString) (i : ℤ) : CompositionSymbol S R :=
  {certificate := if 0 ≤ i then word[i.toNat]? else none}

def compositionIndex (n : ℕ) (i : ℤ) : CompositionSymbol S R :=
  {index := decide (0 ≤ i ∧ i < (n : ℤ))}

@[simp] theorem compositionCertificate_nat (word : BitString) (i : ℕ) :
    compositionCertificate S R word i = {certificate := word[i]?} := by simp [compositionCertificate]

@[simp] theorem compositionCertificate_nil : compositionCertificate S R [] = fun _ => {} := by
  funext i
  simp [compositionCertificate]

@[simp] theorem compositionCertificate_end (word : BitString) :
    compositionCertificate S R word word.length = {} := by simp

theorem compositionCertificate_append (word : BitString) (bit : Bool) :
    Function.update (compositionCertificate S R word) (word.length : ℤ) {certificate := some bit} =
      compositionCertificate S R (word ++ [bit]) := by
  funext i
  cases i with
  | ofNat n =>
      by_cases inside : n < word.length
      · have ne : (n : ℤ) ≠ (word.length : ℤ) := by omega
        simp [Function.update_of_ne ne, List.getElem?_append_left inside]
      · by_cases atEnd : n = word.length
        · simp [atEnd, List.getElem?_append_right]
        · have outside : word.length + 1 ≤ n := by omega
          have ne : (n : ℤ) ≠ (word.length : ℤ) := by omega
          simp [Function.update_of_ne ne, List.getElem?_eq_none (by omega : word.length ≤ n),
            List.getElem?_eq_none (by simpa using outside : (word ++ [bit]).length ≤ n)]
  | negSucc n =>
      have ne : Int.negSucc n ≠ (word.length : ℤ) := by omega
      simp [Function.update_of_ne ne, compositionCertificate]

omit S R in
theorem clampedReadMove_correct (length head : ℕ) (bound : head ≤ length) (move : Move) :
    (clampedReadMove (decide ((head : ℤ) = 0)) (decide (head < length)) move).onInt head =
      ((move.onInput length head : ℕ) : ℤ) := by
  cases move with
  | left =>
      by_cases zero : head = 0 <;> simp [clampedReadMove, Move.onInt, Move.onInput, zero] <;> omega
  | stay => simp [clampedReadMove, Move.onInt, Move.onInput, Nat.min_eq_left bound]
  | right =>
      by_cases inside : head < length <;> simp [clampedReadMove, Move.onInt, Move.onInput, inside] <;> omega

def samplerBankConfiguration (n : ℕ) (source : Configuration S) : CompositionConfiguration S R where
  state := .sample source.state
  inputHead := 0
  auxiliaryHead := 0
  indexHead := n
  randomHead := source.randomHead
  output := []
  head := fun j => if j = 0 then source.workHead else if j = 1 then source.indexHead
    else if j = 2 then source.output.length else 0
  tape := fun j i => if j = 0 then {sampler := source.work i} else if j = 1 then compositionIndex S R n i
    else if j = 2 then compositionCertificate S R source.output i else {}

def recovererBankConfiguration (n : ℕ) (certificate : BitString) (samplerWork : ℤ → Option (Fin S.symbols))
    (samplerHead : ℤ) (source : Configuration R) : CompositionConfiguration S R where
  state := .recover source.state
  inputHead := 0
  auxiliaryHead := 0
  indexHead := n
  randomHead := source.randomHead
  output := source.output
  head := fun j => if j = 0 then samplerHead else if j = 1 then source.indexHead
    else if j = 2 then source.auxiliaryHead else source.workHead
  tape := fun j i => if j = 0 then {sampler := samplerWork i} else if j = 1 then compositionIndex S R n i
    else if j = 2 then compositionCertificate S R certificate i else {recoverer := source.work i}

end
end ComplexityOfGenerators.Simulation
