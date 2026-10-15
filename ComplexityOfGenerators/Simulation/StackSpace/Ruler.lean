import ComplexityOfGenerators.Simulation.StackSpace.Power
import ComplexityOfGenerators.Simulation.StackSpace.MapTransfer
import ComplexityOfGenerators.Simulation.StackSpace.Constants

/-! Initialize a polynomial ruler from the length of a preserved input
stack. Slots 1 and 2 hold the resulting ruler and the factor `n + 1`; slots
3 and 4 are scratch and are empty at return. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

/-- A fixed program for `p(n) = coefficient * (n + 1)^degree`. Both the
coefficient and degree belong to the program; `n` is read from the input.
The bound includes input copying, the unary factor and all partial products. -/
theorem polynomial_ruler (P : Q → Stmt S Q (V × Option S) k)
    (slots : Fin 5 ↪ Fin (k + 1)) (symbol : S) (p : PolynomialBound)
    (copyInput duplicateInput mapInput seed : Q)
    (phase : ℕ → Q) (copy duplicate restore : Fin p.degree → Q)
    (copyInputTable : P copyInput = transferCode (slots 0) (slots 4) copyInput duplicateInput (fun _ => true))
    (duplicateInputTable : P duplicateInput = duplicateCode (slots 4) (slots 0) (slots 1) duplicateInput mapInput)
    (mapInputTable : P mapInput = mapTransferCode (slots 1) (slots 2) mapInput seed (fun _ => symbol))
    (seedTable : P seed = .push (slots 2) (fun _ => symbol)
      (pushCopies (slots 1) symbol p.coefficient (.goto fun _ => phase 0)))
    (scanTable : ∀ i : Fin p.degree, P (phase i.val) = multiplyScan (slots 1) (copy i) (restore i))
    (copyTable : ∀ i, P (copy i) = transferCode (slots 2) (slots 4) (copy i) (duplicate i) (fun _ => true))
    (duplicateTable : ∀ i, P (duplicate i) = duplicateCode (slots 4) (slots 2) (slots 3) (duplicate i) (phase i.val))
    (restoreTable : ∀ i, P (restore i) = transferCode (slots 3) (slots 1) (restore i) (phase (i.val + 1)) (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S)
    (empty : ∀ j : Fin 5, j ≠ 0 → stk (slots j) = []) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) (inputRoom : (stk (slots 0)).length + 1 ≤ r)
    (rulerRoom : p (stk (slots 0)).length ≤ r) :
    Trace P r (localConfig copyInput v stk)
      (localConfig (phase p.degree) v
        (Function.update (Function.update stk (slots 2)
          (List.replicate ((stk (slots 0)).length + 1) symbol)) (slots 1)
          (List.replicate (p (stk (slots 0)).length) symbol))) := by
  have ne {i j : Fin 5} (h : i ≠ j) : slots i ≠ slots j := fun eq => h (slots.injective eq)
  have e₁ := empty 1 (by decide)
  have e₂ := empty 2 (by decide)
  have e₃ := empty 3 (by decide)
  have e₄ := empty 4 (by decide)
  let n := (stk (slots 0)).length
  have first := copy_all P (slots 4) (slots 0) (slots 1) duplicateInput mapInput copyInput
    copyInputTable duplicateInputTable (ne (by decide)) (ne (by decide)) (ne (by decide))
    v stk e₄ r bound (by simpa [e₁] using bound (slots 0))
  let copied := Function.update stk (slots 1) (stk (slots 0))
  have first' : Trace P r (localConfig copyInput v stk) (localConfig mapInput v copied) := by
    simpa only [e₁, List.append_nil] using first
  have mapped := mapTransfer_all P (slots 1) (slots 2) (ne (by decide)) mapInput seed
    (fun _ => symbol) mapInputTable v copied r first'.end_bound (by
      simpa [copied, ne (show (2 : Fin 5) ≠ 1 by decide), e₂] using bound (slots 0))
  let zeros := Function.update stk (slots 2) (List.replicate n symbol)
  have mappedFinish : replaceTwo copied (slots 1) (slots 2) []
      ((copied (slots 1)).reverse.map (fun _ => symbol) ++ copied (slots 2)) = zeros := by
    simp only [copied, Function.update_self, Function.update_of_ne (ne (show (2 : Fin 5) ≠ 1 by decide)),
      e₂, List.append_nil, List.map_const', List.length_reverse]
    simp only [replaceTwo, Function.update_idem, ← e₁, Function.update_eq_self]
    rfl
  rw [mappedFinish] at mapped
  let prepared := Function.update (Function.update stk (slots 2) (List.replicate (n + 1) symbol))
    (slots 1) (List.replicate p.coefficient symbol)
  have seeded : TM2.step P (localConfig seed v zeros) = some (localConfig (phase 0) v prepared) := by
    simp only [TM2.step, localConfig, seedTable, TM2.stepAux, pushCopies_stepAux]
    simp [zeros, prepared, ne (show (1 : Fin 5) ≠ 2 by decide),
      e₁, List.replicate_succ]
  have coeff : p.coefficient ≤ r := by
    have h : 1 ≤ (n + 1) ^ p.degree := Nat.one_le_pow _ _ (by omega)
    change p.coefficient * (n + 1) ^ p.degree ≤ r at rulerRoom
    nlinarith
  have preparedBound : ∀ j, (prepared j).length ≤ r := by
    intro j
    by_cases h₁ : j = slots 1
    · subst j; simpa [prepared] using coeff
    · by_cases h₂ : j = slots 2
      · subst j; simpa [prepared, h₁] using inputRoom
      · simpa [prepared, h₁, h₂] using bound j
  have powered := power_trace P (slots 1) (slots 2) (slots 3) (slots 4)
    (ne (by decide)) (ne (by decide)) (ne (by decide))
    (ne (by decide)) (ne (by decide)) (ne (by decide)) p.degree phase copy duplicate restore
    scanTable copyTable duplicateTable restoreTable v prepared symbol p.coefficient (n + 1) (by omega)
    (by simp [prepared])
    (by simp [prepared, ne (show (2 : Fin 5) ≠ 1 by decide)])
    (by simp [prepared, ne (show (3 : Fin 5) ≠ 1 by decide), ne (show (3 : Fin 5) ≠ 2 by decide), e₃])
    (by simp [prepared, ne (show (4 : Fin 5) ≠ 1 by decide), ne (show (4 : Fin 5) ≠ 2 by decide), e₄])
    r preparedBound rulerRoom
  have complete := first'.trans (mapped.trans (.step mapped.end_bound seeded powered))
  simpa only [prepared, Function.update_idem, PolynomialBound.eval] using complete

end ComplexityOfGenerators.Simulation.StackSpace
