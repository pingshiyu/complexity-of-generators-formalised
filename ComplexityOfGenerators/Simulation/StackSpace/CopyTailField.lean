import ComplexityOfGenerators.Simulation.StackSpace.CopyField
import ComplexityOfGenerators.Simulation.StackSpace.DropLast

/-! Copy all but the first symbol of a delimited field. This is the native
operation that decreases the recursion level when a child frame is pushed. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

theorem copy_tail_field (P : Q → Stmt S Q (V × Option S) k)
    (source target register scratch : Fin (k + 1))
    (sr : source ≠ register) (st : source ≠ scratch) (rt : register ≠ scratch)
    (tr : target ≠ register)
    (read mark copy restore forward trim backward store transfer exit : Q)
    (delimiter : S) (keep : S → Bool)
    (readTable : P read = transferCode source register read mark keep)
    (markTable : P mark = .push source (fun _ => delimiter) (.goto fun _ => copy))
    (copyTable : P copy = duplicateCode register scratch source copy restore)
    (restoreTable : P restore = transferCode scratch register restore forward (fun _ => true))
    (forwardTable : P forward = transferCode register scratch forward trim (fun _ => true))
    (trimTable : P trim = .pop scratch (fun v _ => v) (.goto fun _ => backward))
    (backwardTable : P backward = transferCode scratch register backward store (fun _ => true))
    (storeTable : P store = .push target (fun _ => delimiter) (.goto fun _ => transfer))
    (transferTable : P transfer = mapTransferCode register target transfer exit id)
    (v : V) (stk : Fin (k + 1) → List S) (word suffix : List S)
    (head : stk source = word ++ delimiter :: suffix)
    (more : ∀ s ∈ word, keep s = true) (stop : keep delimiter = false)
    (registerEmpty : stk register = []) (scratchEmpty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r)
    (room : word.tail.length + 1 + (stk target).length ≤ r) :
    Trace P r (localConfig read v stk)
      (localConfig exit v (Function.update stk target (word.tail ++ delimiter :: stk target))) := by
  have first := read_field P source register scratch sr st rt read mark copy restore forward
    delimiter keep readTable markTable copyTable restoreTable v stk word suffix head more stop
    registerEmpty scratchEmpty r bound
  let loaded := Function.update stk register word.reverse
  have trimmed := drop_last P register scratch rt forward trim backward store forwardTable
    trimTable backwardTable v loaded word (by simp [loaded])
    (by simp [loaded, rt.symm, scratchEmpty]) r first.end_bound
  have last := push_field P register target tr.symm transfer exit id store delimiter storeTable
    transferTable v (Function.update loaded register word.tail.reverse) word.tail (by simp)
    r trimmed.end_bound (by simpa [loaded, tr] using room)
  have finish : replaceTwo (Function.update loaded register word.tail.reverse) register target []
      (word.tail.map id ++ delimiter :: (Function.update loaded register word.tail.reverse) target) =
      Function.update stk target (word.tail ++ delimiter :: stk target) := by
    simp only [loaded, Function.update_of_ne tr, replaceTwo, Function.update_idem, List.map_id]
    rw [← registerEmpty, Function.update_eq_self]
  rw [finish] at last
  exact first.trans (trimmed.trans last)

end ComplexityOfGenerators.Simulation.StackSpace
