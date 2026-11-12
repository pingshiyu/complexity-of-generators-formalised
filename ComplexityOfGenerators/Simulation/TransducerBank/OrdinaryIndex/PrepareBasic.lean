import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

def preparing (loaded position : ℕ) (phase : Phase Q S k) :
    BankConfiguration O (Phase Q S k) (Cell (S := S)) (k + 1) :=
  { (bank B).initialConfiguration with
    state := phase
    inputHead := position
    head := Fin.lastCases (position : ℤ) (fun _ => 0)
    tape := Fin.lastCases (indexTape B loaded) (fun _ _ => .inl B.blank) }

theorem indexTape_zero : indexTape B 0 = fun _ => .inl B.blank := by
  funext p
  have outside : ¬ (0 ≤ p ∧ p < (0 : ℤ)) := by omega
  simp [indexTape, outside]

theorem indexTape_update (loaded : ℕ) :
    Function.update (indexTape B loaded) (loaded : ℤ) (.inr ()) = indexTape B (loaded + 1) := by
  funext p
  by_cases same : p = (loaded : ℤ)
  · subst p; simp [indexTape]
  · by_cases early : 0 ≤ p ∧ p < (loaded : ℤ)
    · simp [Function.update_of_ne same, indexTape, early]; omega
    · simp [Function.update_of_ne same, indexTape, early]; omega

theorem preparing_zero : preparing B 0 0 .load = (bank B).initialConfiguration := by
  apply BankConfiguration.ext <;> simp [preparing, TapeBank.initialConfiguration, bank]
  · funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · funext j p
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [indexTape_zero]

theorem preparing_ready (data : InputData I A) :
    preparing B data.input.length 0 (.fetch B.initial) =
      configuration B data B.initialConfiguration := by
  rfl

/-- Write one real index mark while reading one real ordinary input symbol. -/
theorem loading_step (data : InputData I A) (bits : BitString) (loaded : ℕ)
    (live : loaded < data.input.length) :
    (bank B).Steps data bits (preparing B loaded loaded .load) 1
      (preparing B (loaded + 1) (loaded + 1) .load) := by
  have available : data.input[loaded]?.isSome = true := by
    exact Option.isSome_iff_exists.mpr ⟨data.input[loaded], List.getElem?_eq_getElem live⟩
  have instruction : (bank B).instruction data (preparing B loaded loaded .load) =
      .step .load (.inr ()) .right .right .stay .stay none := by
    simp [TapeBank.instruction, preparing, TapeBank.initialConfiguration, bank, available]
  have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
  have same : (bank B).advance data (preparing B loaded loaded .load)
      .load (.inr ()) .right .right .stay .stay none =
      preparing B (loaded + 1) (loaded + 1) .load := by
    apply BankConfiguration.ext <;>
      simp only [TapeBank.advance, preparing, bank, TapeBank.initialConfiguration,
        Move.onInput, Move.onInt, Nat.zero_min, Option.toList_none, List.append_nil]
    · omega
    · rw [Fin.lastCases_last, Fuel.lastCases_update_last]
      congr 1
    · rw [Fin.lastCases_last, Fin.lastCases_last, indexTape_update,
        Fuel.lastCases_update_last]
  simpa only [same] using actual

/-- The output-free rewind synchronizes the real input head with the index head. -/
theorem rewind_step (data : InputData I A) (bits : BitString) (loaded position : ℕ) :
    (bank B).Steps data bits (preparing B loaded (position + 1) .rewind) 1
      (preparing B loaded position .rewind) := by
  have instruction : (bank B).instruction data (preparing B loaded (position + 1) .rewind) =
      .step .rewind (indexTape B loaded (position + 1)) .left .left .stay .stay none := by
    simp [TapeBank.instruction, preparing, TapeBank.initialConfiguration, bank] <;> omega
  have actual := TapeBank.Steps.single (bank B) data bits _ _ _ _ _ _ _ _ instruction
  have same : (bank B).advance data (preparing B loaded (position + 1) .rewind)
      .rewind (indexTape B loaded (position + 1)) .left .left .stay .stay none =
      preparing B loaded position .rewind := by
    apply BankConfiguration.ext <;>
      simp only [TapeBank.advance, preparing, bank, TapeBank.initialConfiguration,
        Move.onInput, Move.onInt, Nat.zero_min, Option.toList_none, List.append_nil]
    · omega
    · rw [Fin.lastCases_last, Fuel.lastCases_update_last]
      congr 1
      omega
    · rw [Fin.lastCases_last, Fin.lastCases_last]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [Function.update_eq_self, Fuel.lastCases_update_last]
  simpa only [same] using actual

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
