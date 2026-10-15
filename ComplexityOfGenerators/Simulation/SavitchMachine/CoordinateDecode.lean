import ComplexityOfGenerators.Simulation.SavitchMachine.BoundedDecode
import ComplexityOfGenerators.Simulation.StackSpace.Embed
import ComplexityOfGenerators.Simulation.StackSpace.MapTransfer

/-! The actual fixed-width coordinate decoder. A length check precedes the
bounded binary conversion, so this program implements both rejection tests
in `FixedWidthCodec.fin`. Its finite control is independent of the field width. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateDecode

open Turing StackSpace Frames
open BoundedDecode (unary registers)
set_option backward.isDefEq.respectTransparency false

inductive Label
  | copyInput | duplicateInput | mapInput | copyBound | duplicateBound
  | startCompare | compare | clear | dispatch
  | decode (pc : BoundedDecode.Label)
  deriving DecidableEq, Fintype

def program : Label → Stmt Symbol Label Local 4
  | .copyInput => transferCode 0 4 .copyInput .duplicateInput (fun _ => true)
  | .duplicateInput => duplicateCode 4 0 3 .duplicateInput .mapInput
  | .mapInput => mapTransferCode 3 4 .mapInput .copyBound (fun _ => some false)
  | .copyBound => transferCode 2 1 .copyBound .duplicateBound (fun _ => true)
  | .duplicateBound => duplicateCode 1 2 3 .duplicateBound .startCompare
  | .startCompare => .load (fun v => ({v.1 with returned := some true}, none)) (.goto fun _ => .compare)
  | .compare => compareCode 4 3 .compare .clear
  | .clear => clearCode 3 .clear .dispatch (fun _ => true)
  | .dispatch => .branch (fun v => v.1.returned.getD false)
      (.load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .decode .read))
      (.load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .decode .done))
  | .decode pc => embedCode (Function.Embedding.refl _) Label.decode (BoundedDecode.program pc)

/-- The length test uses only copies. It leaves the original bit field and
bound intact and restores the three temporary registers to empty. -/
theorem length_test (answer : Bool) (input : List Symbol) (bound r : ℕ)
    (hi : input.length ≤ r) (hb : bound ≤ r) :
    Trace program r (localConfig .copyInput (carrying answer false) (registers input 0 bound))
      (localConfig .dispatch (carrying answer (decide (input.length = bound)))
        (registers input 0 bound)) := by
  let original := registers input 0 bound
  have initial := BoundedDecode.registers_bound input 0 bound r hi (by omega) hb
  have copied := copy_all program 4 0 3 .duplicateInput .mapInput .copyInput rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) original rfl r initial (by
      simpa [original, registers] using hi)
  let withInput : Fin 5 → List Symbol := ![input, [], unary bound, input, []]
  have copiedMemory : Function.update original (3 : Fin 5) (original 0 ++ original 3) = withInput := by
    funext j
    fin_cases j <;> simp [original, registers, withInput, Function.update_apply]
  rw [copiedMemory] at copied
  have mapped := mapTransfer_all program 3 4 (by decide) .mapInput .copyBound (fun _ => some false) rfl
    (carrying answer false) withInput r copied.end_bound (by simpa [withInput] using hi)
  let withLength : Fin 5 → List Symbol := ![input, [], unary bound, [], unary input.length]
  have mappedMemory : replaceTwo withInput (3 : Fin 5) 4 []
      ((withInput 3).reverse.map (fun _ => some false) ++ withInput 4) = withLength := by
    funext j
    fin_cases j <;> simp [withInput, withLength, replaceTwo, Function.update_apply, List.map_const']
  rw [mappedMemory] at mapped
  have copiedBound := copy_all program 1 2 3 .duplicateBound .startCompare .copyBound rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) withLength rfl r mapped.end_bound (by
      simpa [withLength] using hb)
  let withBoth : Fin 5 → List Symbol := ![input, [], unary bound, unary bound, unary input.length]
  have boundMemory : Function.update withLength (3 : Fin 5) (withLength 2 ++ withLength 3) = withBoth := by
    funext j
    fin_cases j <;> simp [withLength, withBoth, Function.update_apply]
  rw [boundMemory] at copiedBound
  have begin : TM2.step program (localConfig .startCompare (carrying answer false) withBoth) =
      some (localConfig .compare (carrying answer true) withBoth) := by
    simp [program, TM2.step, localConfig, TM2.stepAux, carrying]
  have compared := compare_trace program 4 3 (by decide) .compare .dispatch .clear rfl rfl
    answer withBoth r copiedBound.end_bound
  have finishMemory : replaceTwo withBoth (4 : Fin 5) 3 [] [] = original := by
    funext j
    fin_cases j <;> simp [withBoth, original, registers, replaceTwo, Function.update_apply]
  have same : (withBoth 4 = withBoth 3) ↔ input.length = bound := by
    change unary input.length = unary bound ↔ input.length = bound
    constructor
    · intro eq; simpa using congrArg List.length eq
    · rintro eq; rw [eq]
  rw [finishMemory] at compared
  simp only [same] at compared
  exact copied.trans (mapped.trans (copiedBound.trans (.step copiedBound.end_bound begin compared)))

/-- The bounded decoder is embedded with the same five registers, and its
exit label remains available to the enclosing configuration test. -/
theorem decode_trace (answer : Bool) (bits : List Bool) (bound r : ℕ)
    (inputRoom : bits.length ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    Trace program r
      (localConfig (.decode .read) (carrying answer false) (registers (bits.reverse.map some) 0 bound))
      (localConfig (.decode .done) (carrying answer (decide (Complexity.binValLE bits < bound)))
        (registers [] (min bound (Complexity.binValLE bits)) bound)) := by
  have trace := (BoundedDecode.decode_bounded answer bits bound r inputRoom counterRoom).embed_active
    (by simp [localConfig]) (Function.Embedding.refl (Fin 5)) Label.decode program (fun _ _ => rfl)
    (fun _ => []) (by intro j; simp)
  have memory (stk : Fin 5 → List Symbol) :
      Function.extend (Function.Embedding.refl (Fin 5)) stk (fun _ => []) = stk := by
    funext j
    exact (Function.Embedding.refl (Fin 5)).injective.extend_apply stk (fun _ => []) j
  simpa only [embedConfig, localConfig, Option.map_some, memory] using trace

/-- Exact implementation of the fixed-width `Fin bound` decoder. Rejection
of a wrong-length field preserves it for the caller to discard; accepted
coordinates are returned in unary. The bound and scratch invariants hold on
both branches. -/
theorem decode_bounded (answer : Bool) (bits : List Bool) (bound r : ℕ)
    (inputRoom : bits.length ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    ∃ finalInput value,
      Trace program r
        (localConfig .copyInput (carrying answer false) (registers (bits.reverse.map some) 0 bound))
        (localConfig (.decode .done) (carrying answer ((FixedWidthCodec.fin bound).decode bits).isSome)
          (registers finalInput value bound)) ∧
      value ≤ bound ∧
      (∀ coordinate, (FixedWidthCodec.fin bound).decode bits = some coordinate → value = coordinate.val) := by
  have initial := BoundedDecode.registers_bound (bits.reverse.map some) 0 bound r
    (by simp; omega) (by omega) (by omega)
  have first := length_test answer (bits.reverse.map some) bound r (by simp; omega) (by omega)
  simp only [List.length_map, List.length_reverse] at first
  by_cases length : bits.length = bound
  · simp only [length, decide_true] at first
    have next : TM2.step program (localConfig .dispatch (carrying answer true)
        (registers (bits.reverse.map some) 0 bound)) =
        some (localConfig (.decode .read) (carrying answer false) (registers (bits.reverse.map some) 0 bound)) := by
      simp [program, TM2.step, localConfig, TM2.stepAux, carrying]
    have tail := decode_trace answer bits bound r inputRoom counterRoom
    have flag : ((FixedWidthCodec.fin bound).decode bits).isSome = decide (Complexity.binValLE bits < bound) := by
      simp only [FixedWidthCodec.fin, length, true_and]
      split_ifs <;> simp_all
    refine ⟨[], min bound (Complexity.binValLE bits), ?_, Nat.min_le_left _ _, ?_⟩
    · rw [flag]
      exact first.trans (.step first.end_bound next tail)
    · intro coordinate decodes
      have decoded := (FixedWidthCodec.fin_decode_eq_some_iff bound bits coordinate).mp decodes
      simpa only [FixedWidthCodec.bounded_decode_eq] using decoded.2
  · have flag : (FixedWidthCodec.fin bound).decode bits = none := by simp [FixedWidthCodec.fin, length]
    simp only [length, decide_false] at first
    have next : TM2.step program (localConfig .dispatch (carrying answer false)
        (registers (bits.reverse.map some) 0 bound)) =
        some (localConfig (.decode .done) (carrying answer false) (registers (bits.reverse.map some) 0 bound)) := by
      simp [program, TM2.step, localConfig, TM2.stepAux, carrying]
    refine ⟨bits.reverse.map some, 0, ?_, Nat.zero_le _, ?_⟩
    · simp only [flag, Option.isSome_none]
      exact first.trans (.step first.end_bound next (.refl _ initial))
    · intro coordinate decodes
      rw [flag] at decodes
      cases decodes

theorem decode (answer : Bool) (bits : List Bool) (bound : ℕ) :
    ∃ finalInput value,
      Trace program (bits.length + 2 * bound + 1)
        (localConfig .copyInput (carrying answer false) (registers (bits.reverse.map some) 0 bound))
        (localConfig (.decode .done) (carrying answer ((FixedWidthCodec.fin bound).decode bits).isSome)
          (registers finalInput value bound)) ∧
      value ≤ bound ∧
      (∀ coordinate, (FixedWidthCodec.fin bound).decode bits = some coordinate → value = coordinate.val) :=
  decode_bounded answer bits bound _ (by omega) (by omega)

end ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateDecode
