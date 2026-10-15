import ComplexityOfGenerators.Simulation.SavitchMachine.Alphabet
import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateDecode
import ComplexityOfGenerators.Simulation.StackSpace.SkipAffine

/-! Locate and decode a selected configuration-header coordinate, preserving
one previously decoded coordinate and the original input. This is the interface
needed to compare source and target heads without keeping both full decoded
configurations in scratch memory. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

variable {S : Type} [Inhabited S]

inductive Label
  | skip (pc : SkipAffine.Label) | scan | restore | clearSource
  | decode (pc : CoordinateDecode.Label) | done
  deriving DecidableEq, Fintype

def skipSlots : Fin 4 ↪ Fin 7 := ⟨![0, 6, 3, 4], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
def clampSlots : Fin 4 ↪ Fin 7 := ⟨![0, 2, 3, 4], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
def decodeSlots : Fin 5 ↪ Fin 7 := ⟨![3, 0, 2, 4, 5], by
  intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

def program (write : Symbol → S) (read : S → Symbol) (a b : ℕ) :
    Label → Stmt S Label (Status × Option S) 6
  | .skip .done => .goto fun _ => .scan
  | .skip pc => embedCode skipSlots Label.skip (SkipAffine.program (write (some false)) a b pc)
  | .scan => clampCode 0 2 3 4 .scan .restore
  | .restore => transferCode 4 2 .restore .clearSource (fun _ => true)
  | .clearSource => clearCode 0 .clearSource (.decode .copyInput) (fun _ => true)
  | .decode (.decode .done) => clearCode 3 (.decode (.decode .done)) .done (fun _ => true)
  | .decode pc => embedCode decodeSlots Label.decode
      (transportCode write read (Initialize.pack write) (Initialize.unpack read) (CoordinateDecode.program pc))
  | .done => .halt

def before (write : Symbol → S) (bits : List Bool) (saved : List S) (bound : ℕ) (input : List S) : Fin 7 → List S :=
  ![(bits.map some).map write, saved, (unary bound).map write, [], [], [], input]

def after (write : Symbol → S) (value : ℕ) (saved : List S) (bound : ℕ) (input : List S) : Fin 7 → List S :=
  ![(unary value).map write, saved, (unary bound).map write, [], [], [], input]

/-- The selected field is checked with the exact existing codec. The first
coordinate and original input are preserved even when the selected field is
short or invalid; all temporary stacks are empty on return. -/
theorem run (write : Symbol → S) (read : S → Symbol) (inverse : Function.LeftInverse read write)
    (a b : ℕ) (answer : Bool) (bits : List Bool) (saved input : List S) (bound r : ℕ)
    (bitsRoom : bits.length ≤ r) (savedRoom : saved.length ≤ r) (inputRoom : input.length ≤ r)
    (offsetRoom : a * input.length + b ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    ∃ value,
      Trace (program write read a b) r
        (localConfig (.skip .copy) (carrying answer false) (before write bits saved bound input))
        (localConfig .done
          (carrying answer ((FixedWidthCodec.fin bound).decode
            ((bits.drop (a * input.length + b)).take bound)).isSome)
          (after write value saved bound input)) ∧ value ≤ bound ∧
      (∀ coordinate, (FixedWidthCodec.fin bound).decode
        ((bits.drop (a * input.length + b)).take bound) = some coordinate → value = coordinate.val) := by
  let P := program write read a b
  let rest := bits.drop (a * input.length + b)
  let field := rest.take bound
  let original := before write bits saved bound input
  have initial : ∀ j, (original j).length ≤ r := by
    intro j; fin_cases j <;> simp [original, before] <;> omega
  have skipped := (SkipAffine.run (write (some false)) a b (carrying answer false)
    ((bits.map some).map write) input r (by simpa using bitsRoom) inputRoom offsetRoom).embed_active
      (by simp [localConfig]) skipSlots Label.skip P
      (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) original initial
  let ready := before write rest saved bound input
  have firstLayout : Function.extend skipSlots
      (SkipAffine.registers ((bits.map some).map write) input) original = original := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside; rfl
  have skipLayout : Function.extend skipSlots
      (SkipAffine.registers (((bits.map some).map write).drop (a * input.length + b)) input) original = ready := by
    apply extend_eq
    · intro i; fin_cases i <;> simp [skipSlots, SkipAffine.registers, ready, before, rest]
    · intro j outside
      fin_cases j <;> simp_all [skipSlots, Fin.exists_fin_succ, ready, original, before]
  simp only [embedConfig, localConfig, Option.map_some, firstLayout, skipLayout] at skipped
  have handoff : TM2.step P (localConfig (.skip .done) (carrying answer false) ready) =
      some (localConfig .scan (carrying answer false) ready) := rfl
  have extracted := clamp_prefix P clampSlots .scan .restore rfl .restore .clearSource rfl rfl
    (carrying answer false) ready rfl r skipped.end_bound (by
      simp [clampSlots, ready, before]; omega)
  let extractedMemory : Fin 7 → List S :=
    ![((rest.drop bound).map some).map write, saved, (unary bound).map write,
      (field.reverse.map some).map write, [], [], input]
  have extractionLayout : replaceTwo ready (clampSlots 0) (clampSlots 2)
      ((ready (clampSlots 0)).drop (ready (clampSlots 1)).length)
      (((ready (clampSlots 0)).take (ready (clampSlots 1)).length).reverse ++ ready (clampSlots 2)) = extractedMemory := by
    funext j; fin_cases j <;>
      simp [ready, before, extractedMemory, field, clampSlots, replaceTwo, List.map_reverse]
  rw [extractionLayout] at extracted
  have cleared := clear_all P 0 .clearSource (.decode .copyInput) (fun _ => true) rfl
    (carrying answer false) extractedMemory (by simp) r extracted.end_bound
  let prepared : Fin 7 → List S :=
    ![[], saved, (unary bound).map write, (field.reverse.map some).map write, [], [], input]
  have clearLayout : Function.update extractedMemory (0 : Fin 7) [] = prepared := by
    funext j; fin_cases j <;> simp [extractedMemory, prepared]
  rw [clearLayout] at cleared
  obtain ⟨lastInput, value, decoded, valueBound, exactValue⟩ := CoordinateDecode.decode_bounded
    answer field bound r (by dsimp [field, rest]; simp; omega) counterRoom
  have transported := Trace.transport write read (Initialize.pack write) (Initialize.unpack read)
    inverse (Initialize.pack_inverse write read inverse) decoded
  have mapped := transported.embed_active (by simp [transportConfig, localConfig]) decodeSlots Label.decode P
    (by
      intro pc nonhalt
      cases pc with
      | decode pc => cases pc <;> first | rfl | exact False.elim (nonhalt rfl)
      | _ => rfl)
    prepared cleared.end_bound
  let decodedMemory : Fin 7 → List S :=
    ![(unary value).map write, saved, (unary bound).map write, lastInput.map write, [], [], input]
  have decodeFirst : Function.extend decodeSlots
      (fun j => (BoundedDecode.registers (field.reverse.map some) 0 bound j).map write) prepared = prepared := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside; rfl
  have decodeLast : Function.extend decodeSlots
      (fun j => (BoundedDecode.registers lastInput value bound j).map write) prepared = decodedMemory := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside
      fin_cases j <;> simp_all [decodeSlots, Fin.exists_fin_succ, prepared, decodedMemory]
  simp only [embedConfig, transportConfig, localConfig, Initialize.pack,
    Option.map_some, Option.map_none, decodeFirst, decodeLast] at mapped
  have cleaned := clear_all P 3 (.decode (.decode .done)) .done (fun _ => true) rfl
    (carrying answer ((FixedWidthCodec.fin bound).decode field).isSome)
    decodedMemory (by simp) r mapped.end_bound
  have cleanup : Function.update decodedMemory (3 : Fin 7) [] = after write value saved bound input := by
    funext j; fin_cases j <;> simp [decodedMemory, after]
  rw [cleanup] at cleaned
  exact ⟨value, skipped.trans (.step skipped.end_bound handoff (extracted.trans (cleared.trans (mapped.trans cleaned)))),
    valueBound, exactValue⟩

end ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt
