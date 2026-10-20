import ComplexityOfGenerators.Simulation.WordStack.SourceClock
import ComplexityOfGenerators.Simulation.WordStack.Routines

namespace ComplexityOfGenerators.Simulation.WordStack.Source

variable {I A O S Output : Type} {k : ℕ} (M : Machine I A O)

/-- Eleven interpreter registers, three caller inputs, a reversed random block,
a scratch register, and a clock. The injection prevents accidental aliasing. -/
abbrev Layout (k : ℕ) := Fin 17 ↪ Fin k

def bank (slots : Layout k) : Fin 11 ↪ Fin k where
  toFun i := slots ⟨i.val, by omega⟩
  inj' := by intro i j h; have := slots.injective h; exact Fin.ext (congrArg (fun x : Fin 17 => x.val) this)

theorem bank_apply (slots : Layout k) (i : Fin 11) :
    bank slots i = slots ⟨i.val, by omega⟩ := rfl

@[simp] theorem bank_zero (slots : Layout k) : bank slots 0 = slots 0 := rfl

def prepare (slots : Layout k) (initialState : S) (inputMap auxiliaryMap bitMap : S → S)
    (unit : S) : Routine S Output k :=
  (Routine.clearMany ((List.finRange 11).map (bank slots))).seq
  ((Routine.assign (slots 11) (slots 2) (slots 15)
      (by simp) (by simp) (by simp) inputMap).seq
  ((Routine.assign (slots 12) (slots 4) (slots 15)
      (by simp) (by simp) (by simp) auxiliaryMap).seq
  ((Routine.assign (slots 13) (slots 6) (slots 15)
      (by simp) (by simp) (by simp) (fun _ => unit)).seq
  ((Routine.transfer (slots 14) (slots 9) (by simp) bitMap).seq
    (Routine.ofLocal (Local.push (slots 0) initialState))))))

private theorem mem_bank (slots : Layout k) (i : Fin 17) :
    slots i ∈ (List.finRange 11).map (bank slots) ↔ i.val < 11 := by
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, equal⟩
    have equal' := slots.injective equal
    have := congrArg (fun x : Fin 17 => x.val) equal'
    dsimp at this
    omega
  · intro bound
    exact ⟨⟨i.val, bound⟩, rfl⟩

theorem prepare_bank (slots : Layout k) (state unit : S) (f g b : S → S) (s : Local.Store S k)
    (i : Fin 11) :
    (prepare (Output := Output) slots state f g b unit).eval s (bank slots i) =
      match i with
      | 0 => [state]
      | 2 => (s (slots 11)).map f
      | 4 => (s (slots 12)).map g
      | 6 => (s (slots 13)).map (fun _ => unit)
      | 9 => (s (slots 14)).reverse.map b
      | _ => [] := by
  fin_cases i <;> simp only [bank_apply] <;>
    simp [prepare, Routine.seq, Routine.assign_eval, Routine.clearMany_eval,
      Routine.transfer, Routine.ofLocal, Local.eval_push, mem_bank, -List.mem_map]

theorem prepare_external (slots : Layout k) (state unit : S) (f g b : S → S) (s : Local.Store S k)
    (j : Fin k) (outside : ∀ i, j ≠ bank slots i) :
    (prepare (Output := Output) slots state f g b unit).eval s j =
      if j = slots 14 ∨ j = slots 15 then [] else s j := by
  have absent : j ∉ (List.finRange 11).map (bank slots) := by
    simp only [List.mem_map, not_exists, not_and]
    intro i _ eq
    exact outside i eq.symm
  have n0 : j ≠ slots 0 := outside 0
  have n2 : j ≠ slots 2 := outside 2
  have n4 : j ≠ slots 4 := outside 4
  have n6 : j ≠ slots 6 := outside 6
  have n9 : j ≠ slots 9 := outside 9
  by_cases hs : j = slots 14 <;> by_cases ht : j = slots 15 <;>
    simp [prepare, Routine.seq, Routine.assign_eval, Routine.clearMany_eval,
      Routine.transfer, Routine.ofLocal, Local.eval_push, hs, ht, absent, n0, n2, n4, n6, n9,
      Function.update_apply, -List.mem_map]

theorem prepare_initial (slots : Layout k) (encode : Symbol M → S) (f g b : S → S)
    (s : Local.Store S k) (data : InputData I A) (bits : BitString)
    (input_eq : (s (slots 11)).map f = data.input.map (fun a => encode (.input a)))
    (auxiliary_eq : (s (slots 12)).map g = data.auxiliary.map (fun a => encode (.auxiliary a)))
    (index_eq : (s (slots 13)).length = data.index)
    (bits_eq : (s (slots 14)).reverse.map b = bits.map (fun a => encode (.bit a))) :
    (prepare (Output := Output) slots (encode (.state (.live M.initial))) f g b (encode .unit)).eval s ∘ bank slots =
      Local.mapStore encode ((initial M data bits).store M) := by
  funext i
  rw [Function.comp_apply, prepare_bank]
  fin_cases i <;>
    simp [Local.mapStore, initial, Snapshot.store, List.map_map, Function.comp_def,
      input_eq, auxiliary_eq, index_eq, bits_eq]

theorem prepare_cost (slots : Layout k) (state unit : S) (f g b : S → S)
    (s : Local.Store S k) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (prepare (Output := Output) slots state f g b unit).cost s ≤ 100 * (budget + 1) := by
  have clearBound := Routine.clearMany_cost (O := Output) ((List.finRange 11).map (bank slots)) s budget
    (fun j _ => sizes j)
  simp only [List.length_map, List.length_finRange] at clearBound
  have h₁ := sizes (slots 11)
  have h₂ := sizes (slots 12)
  have h₃ := sizes (slots 13)
  have h₄ := sizes (slots 14)
  have h₅ := sizes (slots 15)
  simp only [prepare, Routine.seq, Routine.assign_cost, Routine.assign_eval,
    Routine.transfer, Routine.ofLocal, Local.ticks, Local.push, Routine.clearMany_eval] 
  simp [mem_bank, Function.update_apply, -List.mem_map]
  nlinarith

end ComplexityOfGenerators.Simulation.WordStack.Source
