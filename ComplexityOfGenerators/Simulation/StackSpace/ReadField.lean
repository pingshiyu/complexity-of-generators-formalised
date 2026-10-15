import ComplexityOfGenerators.Simulation.StackSpace.Copy

/-! Read a delimited field into a temporary register, restoring its source.
The two other loops copy the field back cell by cell; the delimiter and all
suspended data are preserved even when the source is a frame column. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Inhabited S]

/-- A field read uses two initially empty registers. One holds the reversed
field on return; the other is again empty. -/
theorem read_field (P : Q → Stmt S Q (V × Option S) k)
    (source register scratch : Fin (k + 1))
    (sr : source ≠ register) (st : source ≠ scratch) (rt : register ≠ scratch)
    (read mark copy restore exit : Q) (delimiter : S) (keep : S → Bool)
    (readTable : P read = transferCode source register read mark keep)
    (markTable : P mark = .push source (fun _ => delimiter) (.goto fun _ => copy))
    (copyTable : P copy = duplicateCode register scratch source copy restore)
    (restoreTable : P restore = transferCode scratch register restore exit (fun _ => true))
    (v : V) (stk : Fin (k + 1) → List S) (word suffix : List S)
    (head : stk source = word ++ delimiter :: suffix)
    (more : ∀ s ∈ word, keep s = true) (stop : keep delimiter = false)
    (registerEmpty : stk register = []) (scratchEmpty : stk scratch = [])
    (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace P r (localConfig read v stk)
      (localConfig exit v (Function.update stk register word.reverse)) := by
  have sourceBound := bound source
  rw [head] at sourceBound
  have wordBound : word.length ≤ r := by
    simp only [List.length_append] at sourceBound; omega
  have first := transfer_field P source register sr read mark keep readTable v stk
    word delimiter suffix head more stop r bound (by simpa [registerEmpty] using wordBound)
  let loaded := replaceTwo stk source register suffix (word.reverse ++ stk register)
  let marked := Function.update loaded source (delimiter :: suffix)
  have markedBound : ∀ j, (marked j).length ≤ r := by
    intro j
    by_cases h : j = source
    · subst j
      simp only [marked, Function.update_self]
      simp only [List.length_append] at sourceBound
      omega
    · simpa only [marked, Function.update_of_ne h] using (show (loaded j).length ≤ r from first.end_bound j)
  have next : TM2.step P (localConfig mark v loaded) = some (localConfig copy v marked) := by
    simp [TM2.step, localConfig, markTable, TM2.stepAux, marked, loaded,
      replaceTwo_get_src _ _ _ sr]
  have last := copy_reverse P scratch register source copy exit restore copyTable restoreTable
    rt.symm st.symm sr.symm v marked
    (by simp [marked, loaded, replaceTwo, st.symm, rt.symm, scratchEmpty]) r markedBound (by
      simpa [marked, loaded, replaceTwo, sr.symm, registerEmpty] using sourceBound)
  have finish : Function.update marked source ((marked register).reverse ++ marked source) =
      Function.update stk register word.reverse := by
    funext j
    by_cases h : j = source
    · subst j
      simp [marked, loaded, replaceTwo, sr, sr.symm, registerEmpty, head]
    · by_cases e : j = register
      · subst j
        simp [marked, loaded, replaceTwo, h, registerEmpty]
      · simp [marked, loaded, replaceTwo, h, e]
  rw [finish] at last
  exact first.trans (.step first.end_bound next last)

end ComplexityOfGenerators.Simulation.StackSpace
