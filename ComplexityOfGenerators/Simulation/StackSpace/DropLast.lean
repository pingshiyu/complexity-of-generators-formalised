import ComplexityOfGenerators.Simulation.StackSpace.Transfer

/-! Remove the last symbol of a register using a temporary stack. This turns
an already reversed field into the reversal of its tail, as needed when
Savitch decreases the unary recursion level. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

theorem drop_last (P : Q → Stmt S Q (V × Option S) k)
    (register scratch : Fin (k + 1)) (different : register ≠ scratch)
    (forward trim backward exit : Q)
    (forwardTable : P forward = transferCode register scratch forward trim (fun _ => true))
    (trimTable : P trim = .pop scratch (fun v _ => v) (.goto fun _ => backward))
    (backwardTable : P backward = transferCode scratch register backward exit (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S) (word : List S)
    (head : stk register = word.reverse) (empty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig forward v stk)
      (localConfig exit v (Function.update stk register word.tail.reverse)) := by
  have first := transfer_all P register scratch different forward trim (fun _ => true)
    forwardTable v stk (by simp) r bound (by simpa [empty] using bound register)
  let reversed := replaceTwo stk register scratch [] word
  have first' : Trace P r (localConfig forward v stk) (localConfig trim v reversed) := by
    simpa only [head, empty, List.append_nil, List.reverse_reverse] using first
  let trimmed := replaceTwo stk register scratch [] word.tail
  have trimmedBound : ∀ j, (trimmed j).length ≤ r := by
    apply replaceTwo_bound stk register scratch r bound [] word.tail (by simp)
    have h := bound register
    rw [head, List.length_reverse] at h
    simp only [List.length_tail]; omega
  have next : TM2.step P (localConfig trim v reversed) = some (localConfig backward v trimmed) := by
    simp [TM2.step, localConfig, trimTable, TM2.stepAux, reversed, trimmed, replaceTwo]
  have last := transfer_all P scratch register different.symm backward exit (fun _ => true)
    backwardTable v trimmed (by simp) r trimmedBound (by
      simpa only [trimmed, replaceTwo_get_src _ _ _ different, replaceTwo_get_dst,
        List.length_nil, Nat.add_zero] using trimmedBound scratch)
  have finish : replaceTwo trimmed scratch register [] ((trimmed scratch).reverse ++ trimmed register) =
      Function.update stk register word.tail.reverse := by
    funext j
    by_cases hr : j = register
    · subst j; simp [trimmed, replaceTwo, different]
    · by_cases hs : j = scratch
      · subst j; simp [trimmed, replaceTwo, hr, empty]
      · simp [trimmed, replaceTwo, hr, hs]
  rw [finish] at last
  exact first'.trans (.step first'.end_bound next last)

end ComplexityOfGenerators.Simulation.StackSpace
