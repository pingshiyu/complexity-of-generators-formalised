import ComplexityOfGenerators.Simulation.StackSpace.SkipAffine
import ComplexityOfGenerators.Simulation.StackSpace.Embed

/-! Locate the work-window suffix while retaining a decoded head and another
window. Two temporary registers suffice: the affine header prefix is skipped
first, then a copy of the preserved work-head width supplies the final skip. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.SkipWorkPrefix

open Turing StackSpace
set_option backward.isDefEq.respectTransparency false
variable {S V : Type} [Inhabited S]

inductive Label | skip (pc : SkipAffine.Label) | copy | duplicate | drop | inspect | done
  deriving DecidableEq, Fintype

def slots : Fin 4 ↪ Fin 7 := ⟨![1, 6, 3, 4], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def program (symbol : S) (states : ℕ) : Label → Stmt S Label (V × Option S) 6
  | .skip .done => .goto fun _ => .copy
  | .skip pc => embedCode slots Label.skip (SkipAffine.program symbol 2 (states + 3) pc)
  | .copy => transferCode 2 4 .copy .duplicate (fun _ => true)
  | .duplicate => duplicateCode 4 2 3 .duplicate .drop
  | .drop => readAtCode 1 3 .drop .inspect
  | .inspect => inspectCode 1 (fun _ v => v) .done
  | .done => .halt

def registers (head code bound other input : List S) : Fin 7 → List S :=
  ![head, code, bound, [], [], other, input]

/-- No code validity is assumed: truncation results in an empty suffix, which
the work-window validator subsequently rejects. The head, width, other window
and original input are preserved exactly. -/
theorem run (symbol : S) (states : ℕ) (v : V) (head code bound other input : List S)
    (r : ℕ) (headRoom : head.length ≤ r) (codeRoom : code.length ≤ r) (boundRoom : bound.length ≤ r)
    (otherRoom : other.length ≤ r) (inputRoom : input.length ≤ r)
    (offsetRoom : 2 * input.length + (states + 3) ≤ r) :
    Trace (program symbol states) r
      (localConfig (.skip .copy) v (registers head code bound other input))
      (localConfig .done v (registers head
        (code.drop (2 * input.length + (states + 3) + bound.length)) bound other input)) := by
  let P := program (V := V) symbol states
  let original := registers head code bound other input
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, registers] <;> assumption
  have skipped := (SkipAffine.run symbol 2 (states + 3) v code input r codeRoom inputRoom offsetRoom).embed_active
    (by simp [localConfig]) slots Label.skip P
    (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) original initial
  let rest := code.drop (2 * input.length + (states + 3))
  let ready := registers head rest bound other input
  have firstLayout : Function.extend slots (SkipAffine.registers code input) original = original := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside; rfl
  have lastLayout : Function.extend slots (SkipAffine.registers rest input) original = ready := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside
      fin_cases j <;> simp_all [slots, Fin.exists_fin_succ, original, registers, ready]
  simp only [embedConfig, localConfig, Option.map_some, firstLayout] at skipped
  change Trace P r (localConfig (.skip .copy) v original)
    (localConfig (.skip .done) v (Function.extend slots (SkipAffine.registers rest input) original)) at skipped
  rw [lastLayout] at skipped
  have copied := copy_all P 4 2 3 .duplicate .drop .copy rfl rfl (by decide) (by decide) (by decide)
    v ready rfl r skipped.end_bound (by simpa [ready, registers] using boundRoom)
  let withCounter : Fin 7 → List S := ![head, rest, bound, bound, [], other, input]
  have copiedLayout : Function.update ready (3 : Fin 7) (ready 2 ++ ready 3) = withCounter := by
    funext j; fin_cases j <;> simp [ready, registers, withCounter]
  rw [copiedLayout] at copied
  have scanned := readAt_trace P 1 3 (by decide) .drop .inspect rfl .done (fun _ v => v) rfl v withCounter r copied.end_bound
  have finalLayout : replaceTwo withCounter (1 : Fin 7) 3 ((withCounter 1).drop (withCounter 3).length) [] =
      registers head (code.drop (2 * input.length + (states + 3) + bound.length)) bound other input := by
    funext j; fin_cases j <;> simp [withCounter, registers, rest, replaceTwo, List.drop_drop]
  rw [finalLayout] at scanned
  exact skipped.trans (.step skipped.end_bound rfl (copied.trans scanned))

end ComplexityOfGenerators.Simulation.SavitchMachine.SkipWorkPrefix
