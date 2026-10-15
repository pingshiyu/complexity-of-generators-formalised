import ComplexityOfGenerators.Simulation.StackSpace.Multiply

/-! A fixed number of unary multiplications constructs polynomial-size
rulers. The exponent is part of the finite program, not a runtime register. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]
variable (P : Q → Stmt S Q (V × Option S) k)
variable (counter factor result scratch : Fin (k + 1))
variable (cf : counter ≠ factor) (cr : counter ≠ result) (cs : counter ≠ scratch)
variable (fr : factor ≠ result) (fs : factor ≠ scratch) (rs : result ≠ scratch)

include cf cr cs fr fs rs

/-- Multiply a unary counter in place, preserving its factor and clearing
the result and scratch registers for the next multiplication. -/
theorem scale_counter (scan copy duplicate restore exit : Q)
    (scanTable : P scan = multiplyScan counter copy restore)
    (copyTable : P copy = transferCode factor scratch copy duplicate (fun _ => true))
    (duplicateTable : P duplicate = duplicateCode scratch factor result duplicate scan)
    (restoreTable : P restore = transferCode result counter restore exit (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S) (symbol : S) (count width : ℕ)
    (counterWord : stk counter = List.replicate count symbol)
    (factorWord : stk factor = List.replicate width symbol)
    (resultEmpty : stk result = []) (scratchEmpty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (room : count * width ≤ r) :
    Trace P r (localConfig scan v stk)
      (localConfig exit v (Function.update stk counter (List.replicate (count * width) symbol))) := by
  have first := multiply_trace P counter factor result scratch cf cr cs fr fs rs
    scan copy duplicate restore scanTable copyTable duplicateTable v stk scratchEmpty r bound (by
      simpa [counterWord, factorWord, resultEmpty] using room)
  let middle := replaceTwo stk counter result [] (List.replicate (count * width) symbol)
  have first' : Trace P r (localConfig scan v stk) (localConfig restore v middle) := by
    simpa only [counterWord, factorWord, resultEmpty, List.length_replicate,
      copies_replicate, List.append_nil] using first
  have last := transfer_all P result counter cr.symm restore exit (fun _ => true)
    restoreTable v middle (by simp) r first'.end_bound (by
      simpa [middle, replaceTwo, cr] using room)
  have finish : replaceTwo middle result counter [] ((middle result).reverse ++ middle counter) =
      Function.update stk counter (List.replicate (count * width) symbol) := by
    funext j
    by_cases hc : j = counter
    · subst j; simp [middle, replaceTwo, cr]
    · by_cases hr : j = result
      · subst j; simp [middle, replaceTwo, hc, resultEmpty]
      · simp [middle, replaceTwo, hc, hr]
  rw [finish] at last
  exact first'.trans last

/-- `degree` is fixed when the program is built. Every intermediate unary
counter is at most the final polynomial value when the factor is positive. -/
theorem power_trace (degree : ℕ) (phase : ℕ → Q) (copy duplicate restore : Fin degree → Q)
    (scanTable : ∀ i : Fin degree, P (phase i.val) = multiplyScan counter (copy i) (restore i))
    (copyTable : ∀ i, P (copy i) = transferCode factor scratch (copy i) (duplicate i) (fun _ => true))
    (duplicateTable : ∀ i, P (duplicate i) = duplicateCode scratch factor result (duplicate i) (phase i.val))
    (restoreTable : ∀ i, P (restore i) = transferCode result counter (restore i) (phase (i.val + 1)) (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S) (symbol : S) (coefficient width : ℕ)
    (positive : 1 ≤ width)
    (counterWord : stk counter = List.replicate coefficient symbol)
    (factorWord : stk factor = List.replicate width symbol)
    (resultEmpty : stk result = []) (scratchEmpty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) (room : coefficient * width ^ degree ≤ r) :
    Trace P r (localConfig (phase 0) v stk)
      (localConfig (phase degree) v
        (Function.update stk counter (List.replicate (coefficient * width ^ degree) symbol))) := by
  have walk (i : ℕ) (hi : i ≤ degree) :
      Trace P r (localConfig (phase 0) v stk)
        (localConfig (phase i) v (Function.update stk counter (List.replicate (coefficient * width ^ i) symbol))) := by
    induction i with
    | zero =>
        simp only [pow_zero, Nat.mul_one, ← counterWord, Function.update_eq_self]
        exact .refl _ bound
    | succ i ih =>
        have first := ih (by omega)
        let ix : Fin degree := ⟨i, by omega⟩
        have last := scale_counter P counter factor result scratch cf cr cs fr fs rs
          (phase i) (copy ix) (duplicate ix) (restore ix) (phase (i + 1))
          (scanTable ix) (copyTable ix) (duplicateTable ix) (restoreTable ix)
          v (Function.update stk counter (List.replicate (coefficient * width ^ i) symbol))
          symbol (coefficient * width ^ i) width (by simp)
          (by simpa [cf.symm] using factorWord)
          (by simpa [cr.symm] using resultEmpty)
          (by simpa [cs.symm] using scratchEmpty) r first.end_bound (by
            rw [Nat.mul_assoc, ← pow_succ]
            exact (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_right positive hi)).trans room)
        simpa only [Function.update_idem, Nat.mul_assoc, ← pow_succ] using first.trans last
  exact walk degree (by rfl)

end ComplexityOfGenerators.Simulation.StackSpace
