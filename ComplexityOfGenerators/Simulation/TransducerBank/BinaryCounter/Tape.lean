import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter

theorem one_index (index : Fin 1) : index=0 := Fin.ext (by have := index.isLt; omega)

theorem digitTape_at (low high : List Bool) : digitTape (low++high) low.length=high.head? := by
  cases high <;> simp [digitTape,List.getElem?_append_right]

theorem digitTape_write (low high : List Bool) (bit : Bool) :
    Function.update (digitTape (low++high)) (low.length : ℤ) (some bit)=
      digitTape (low++bit::high.tail) := by
  funext position
  by_cases same : position=(low.length : ℤ)
  · subst position
    simp [digitTape_at]
  · rw [Function.update_of_ne same]
    by_cases nonnegative : 0≤position
    · simp only [digitTape,ite_eq_left nonnegative]
      by_cases before : position.toNat<low.length
      · rw [List.getElem?_append_left before,List.getElem?_append_left before]
      · have later : low.length≤position.toNat := by omega
        have positive : 0<position.toNat-low.length := by omega
        rw [List.getElem?_append_right later,List.getElem?_append_right later]
        have splitIndex : position.toNat-low.length=(position.toNat-low.length-1)+1 := by omega
        rw [splitIndex,List.getElem?_cons_succ,List.getElem?_tail]
    · simp [digitTape,nonnegative]

theorem instruction_carry {I A O : Type} (data : InputData I A) (low high : List Bool) :
    (bank I A O).instruction data (encoded (low++high) low.length .carry)=
      if high.head?=some true then .step .carry (some false) .right .stay .stay .stay none
      else .step .rewind (some true) .stay .stay .stay .stay none := by
  simp [TapeBank.instruction,bank,encoded,transition,digitTape_at]

theorem advance_write {I A O : Type} (data : InputData I A) (low high : List Bool)
    (phase next : Phase) (bit : Bool) (work : Move) (position : ℕ)
    (moved : work.onInt (low.length : ℤ)=(position : ℤ)) :
    (bank I A O).advance data (encoded (low++high) low.length phase) next (some bit)
      work .stay .stay .stay none=encoded (low++bit::high.tail) position next := by
  apply BankConfiguration.ext <;> try rfl
  all_goals try { simp [TapeBank.advance,encoded,Move.onInput] }
  · funext index
    rw [one_index index]
    simpa [TapeBank.advance,encoded,bank] using moved
  · funext index
    rw [one_index index]
    simpa [TapeBank.advance,encoded,bank] using digitTape_write low high bit

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter
