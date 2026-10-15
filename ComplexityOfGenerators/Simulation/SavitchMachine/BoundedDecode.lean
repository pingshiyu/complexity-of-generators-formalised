import ComplexityOfGenerators.Simulation.StackSpace.Clamp
import ComplexityOfGenerators.Simulation.StackSpace.Expand
import ComplexityOfGenerators.Simulation.SavitchMachine.Compare
import ComplexityOfGenerators.Foundations.BoundedCoordinate

/-! A finite stack program for bounded binary-to-unary conversion. The input
field is read most significant bit first, as provided by the frame loader.
Every digit is clamped to a preserved unary bound. Thus invalid midpoint
coordinates cannot cause exponential space use. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.BoundedDecode

open Turing StackSpace Frames
set_option backward.isDefEq.respectTransparency false

inductive Label
  | read | double | add | clamp | restore | clear
  | copyValue | duplicateValue | copyBound | duplicateBound | startCompare
  | compare | clearCompare | verdict | done
  deriving DecidableEq, Fintype

abbrev unary (n : ℕ) : List Symbol := List.replicate n (some false)

def registers (input : List Symbol) (value bound : ℕ) : Fin 5 → List Symbol :=
  ![input, unary value, unary bound, [], []]

def clampSlots : Fin 4 ↪ Fin 5 := ⟨![3, 2, 1, 4], by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all⟩

def program : Label → Stmt Symbol Label Local 4
  | .read => .pop 0 (fun v s => (v.1, s))
      (.branch (fun v => v.2.isSome)
        (.branch (fun v => v.2.join.isSome)
          (.load (fun v => ({v.1 with returned := v.2.join}, none)) (.goto fun _ => .double))
          (.load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)))
        (.load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .copyValue)))
  | .double => expandCode 1 3 (some false) 2 .double .add
  | .add => .branch (fun v => v.1.returned.getD false)
      (.push 3 (fun _ => some false) (.goto fun _ => .clamp)) (.goto fun _ => .clamp)
  | .clamp => clampCode 3 2 1 4 .clamp .restore
  | .restore => transferCode 4 2 .restore .clear (fun _ => true)
  | .clear => clearCode 3 .clear .read (fun _ => true)
  | .copyValue => transferCode 1 0 .copyValue .duplicateValue (fun _ => true)
  | .duplicateValue => duplicateCode 0 1 4 .duplicateValue .copyBound
  | .copyBound => transferCode 2 0 .copyBound .duplicateBound (fun _ => true)
  | .duplicateBound => duplicateCode 0 2 3 .duplicateBound .startCompare
  | .startCompare => .load (fun v => ({v.1 with returned := some true}, none)) (.goto fun _ => .compare)
  | .compare => compareCode 4 3 .compare .clearCompare
  | .clearCompare => clearCode 3 .clearCompare .verdict (fun _ => true)
  | .verdict => .load (fun v => ({v.1 with returned := some (!v.1.returned.getD false)}, none))
      (.goto fun _ => .done)
  | .done => .halt

theorem registers_bound (input : List Symbol) (value bound r : ℕ)
    (hi : input.length ≤ r) (hv : value ≤ r) (hb : bound ≤ r) :
    ∀ j, (registers input value bound j).length ≤ r := by
  intro j
  fin_cases j <;> simp [registers] <;> assumption

/-- One Horner step uses at most `2 * value + 1` cells on the expansion
stack and at most `bound` on the value and scratch stacks. -/
theorem digit (answer bit : Bool) (input : List Symbol) (value bound r : ℕ)
    (hi : input.length ≤ r) (hv : 2 * value + 1 ≤ r) (hb : bound ≤ r) :
    Trace program r (localConfig .double (carrying answer bit) (registers input value bound))
      (localConfig .read (carrying answer bit)
        (registers input (FixedWidthCodec.boundedDigit bound value bit) bound)) := by
  have initial := registers_bound input value bound r hi (by omega) hb
  have expanded := expand_all program 1 3 (by decide) (some false) 2 .double .add rfl
    (carrying answer bit) (registers input value bound) r initial (by simp [registers]; omega)
  let doubled : Fin 5 → List Symbol := ![input, [], unary bound, unary (2 * value), []]
  have expansion : replaceTwo (registers input value bound) (1 : Fin 5) 3 []
      (List.replicate (2 * (registers input value bound 1).length) (some false) ++
        registers input value bound 3) = doubled := by
    funext j
    fin_cases j <;> simp [doubled, registers, replaceTwo, Function.update_apply]
  rw [expansion] at expanded
  let total := 2 * value + if bit then 1 else 0
  let prepared : Fin 5 → List Symbol := ![input, [], unary bound, unary total, []]
  have next : TM2.step program (localConfig .add (carrying answer bit) doubled) =
      some (localConfig .clamp (carrying answer bit) prepared) := by
    cases bit <;> simp [program, TM2.step, localConfig, TM2.stepAux, carrying, doubled, prepared, total]
    funext j
    fin_cases j <;> simp [Function.update_apply, List.replicate_succ]
  have preparedBound : ∀ j, (prepared j).length ≤ r := by
    intro j
    fin_cases j <;> simp [prepared] <;> first | assumption | (dsimp [total]; split_ifs <;> omega)
  have clamped := clamp_all program clampSlots .clamp .restore rfl .restore .clear .read rfl rfl rfl
    (carrying answer bit) prepared rfl r preparedBound (by simp [clampSlots, prepared]; omega)
  have finish : replaceTwo prepared (clampSlots 0) (clampSlots 2) []
      (((prepared (clampSlots 0)).take (prepared (clampSlots 1)).length).reverse ++
        prepared (clampSlots 2)) =
      registers input (FixedWidthCodec.boundedDigit bound value bit) bound := by
    funext j
    fin_cases j <;>
      simp [clampSlots, prepared, registers, replaceTwo, Function.update_apply,
        List.take_replicate, FixedWidthCodec.boundedDigit, total, Nat.min_comm]
  rw [finish] at clamped
  exact expanded.trans (.step expanded.end_bound next clamped)

/-- Read all digits, keeping the same bound and clearing both temporary
registers after each digit. -/
theorem scan (answer carry : Bool) (bits : List Bool) (value bound r : ℕ)
    (hi : bits.length ≤ r) (hv : value ≤ bound) (room : 2 * bound + 1 ≤ r) :
    Trace program r (localConfig .read (carrying answer carry) (registers (bits.map some) value bound))
      (localConfig .copyValue (carrying answer false)
        (registers [] (bits.foldl (FixedWidthCodec.boundedDigit bound) value) bound)) := by
  induction bits generalizing value carry with
  | nil =>
      have initial := registers_bound [] value bound r (by simp) (by omega) (by omega)
      have next : TM2.step program (localConfig .read (carrying answer carry) (registers [] value bound)) =
          some (localConfig .copyValue (carrying answer false) (registers [] value bound)) := by
        simp [program, TM2.step, localConfig, TM2.stepAux, carrying, registers]
      exact .step initial next (.refl _ initial)
  | cons bit bits ih =>
      have initial := registers_bound ((bit :: bits).map some) value bound r (by simpa using hi)
        (by omega) (by omega)
      have next : TM2.step program (localConfig .read (carrying answer carry)
          (registers ((bit :: bits).map some) value bound)) =
          some (localConfig .double (carrying answer bit) (registers (bits.map some) value bound)) := by
        simp [program, TM2.step, localConfig, TM2.stepAux, carrying, registers]
        funext j
        fin_cases j <;> simp [Function.update_apply]
      have tailRoom : bits.length ≤ r := by simp only [List.length_cons] at hi; omega
      have expanded := digit answer bit (bits.map some) value bound r (by simpa using tailRoom)
        (by omega) (by omega)
      have tail := ih bit (FixedWidthCodec.boundedDigit bound value bit) tailRoom (Nat.min_le_left _ _)
      exact .step initial next (expanded.trans tail)

/-- The range test compares copies of the value and bound. It preserves both
unary registers, and clears the two copies and the copying scratch register. -/
theorem validate (answer : Bool) (value bound r : ℕ) (hv : value ≤ bound) (room : bound ≤ r) :
    Trace program r (localConfig .copyValue (carrying answer false) (registers [] value bound))
      (localConfig .done (carrying answer (decide (value < bound))) (registers [] value bound)) := by
  let original := registers [] value bound
  have initial := registers_bound [] value bound r (by simp) (hv.trans room) room
  have copiedValue := copy_all program 0 1 4 .duplicateValue .copyBound .copyValue rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) original rfl r initial (by
      simpa [original, registers] using hv.trans room)
  let withValue : Fin 5 → List Symbol := ![[], unary value, unary bound, [], unary value]
  have valueMemory : Function.update original (4 : Fin 5)
      (original 1 ++ original 4) = withValue := by
    funext j
    fin_cases j <;> simp [original, registers, withValue, Function.update_apply]
  rw [valueMemory] at copiedValue
  have copiedBound := copy_all program 0 2 3 .duplicateBound .startCompare .copyBound rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) withValue rfl r
    copiedValue.end_bound (by simpa [withValue] using room)
  let withBoth : Fin 5 → List Symbol := ![[], unary value, unary bound, unary bound, unary value]
  have boundMemory : Function.update withValue (3 : Fin 5)
      (withValue 2 ++ withValue 3) = withBoth := by
    funext j
    fin_cases j <;> simp [withValue, withBoth, Function.update_apply]
  rw [boundMemory] at copiedBound
  have begin : TM2.step program (localConfig .startCompare (carrying answer false) withBoth) =
      some (localConfig .compare (carrying answer true) withBoth) := by
    simp [program, TM2.step, localConfig, TM2.stepAux, carrying]
  have compared := compare_trace program 4 3 (by decide) .compare .verdict .clearCompare rfl rfl
    answer withBoth r copiedBound.end_bound
  have compareMemory : replaceTwo withBoth (4 : Fin 5) 3 [] [] = original := by
    funext j
    fin_cases j <;> simp [replaceTwo, withBoth, original, registers, Function.update_apply]
  have same : (withBoth 4 = withBoth 3) ↔ value = bound := by
    change List.replicate value (some false) = List.replicate bound (some false) ↔ value = bound
    constructor
    · intro eq; simpa using congrArg List.length eq
    · rintro rfl; rfl
  rw [compareMemory] at compared
  simp only [same] at compared
  have verdict : TM2.step program (localConfig .verdict (carrying answer (decide (value = bound))) original) =
      some (localConfig .done (carrying answer (decide (value < bound))) original) := by
    have flag : (!decide (value = bound)) = decide (value < bound) := by
      by_cases eq : value = bound
      · simp [eq]
      · simp [eq, show value < bound from by omega]
    simp [program, TM2.step, localConfig, TM2.stepAux, carrying, flag]
  exact copiedValue.trans (copiedBound.trans (.step copiedBound.end_bound begin
    (compared.trans (.step compared.end_bound verdict (.refl _ initial)))))

/-- Complete bounded decoding of a little-endian configuration field. The
source is consumed, the bound is preserved, and all temporary registers are
empty. Both accepted and rejected inputs use the same linear space bound. -/
theorem decode_bounded (answer : Bool) (bits : List Bool) (bound r : ℕ)
    (inputRoom : bits.length ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    Trace program r
      (localConfig .read (carrying answer false) (registers (bits.reverse.map some) 0 bound))
      (localConfig .done (carrying answer (decide (Complexity.binValLE bits < bound)))
        (registers [] (min bound (Complexity.binValLE bits)) bound)) := by
  have first := scan answer false bits.reverse 0 bound r
    (by simpa using inputRoom) (by omega) counterRoom
  rw [FixedWidthCodec.bounded_decode_eq] at first
  have last := validate answer (min bound (Complexity.binValLE bits)) bound r
    (Nat.min_le_left _ _) (by omega)
  have valid : (min bound (Complexity.binValLE bits) < bound) ↔ Complexity.binValLE bits < bound := by omega
  simp only [valid] at last
  exact first.trans last

theorem decode (answer : Bool) (bits : List Bool) (bound : ℕ) :
    Trace program (bits.length + 2 * bound + 1)
      (localConfig .read (carrying answer false) (registers (bits.reverse.map some) 0 bound))
      (localConfig .done (carrying answer (decide (Complexity.binValLE bits < bound)))
        (registers [] (min bound (Complexity.binValLE bits)) bound)) :=
  decode_bounded answer bits bound _ (by omega) (by omega)

end ComplexityOfGenerators.Simulation.SavitchMachine.BoundedDecode
