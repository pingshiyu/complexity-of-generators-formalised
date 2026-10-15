import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateDecode

/-! Parse one coordinate from a configuration bitstream. The unary bound also
specifies its fixed width. The unconsumed suffix is preserved, including on
malformed inputs; the extracted field and every temporary register are cleared.
The same finite program handles every width. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinate

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

inductive Label
  | scan | restore | decode (pc : CoordinateDecode.Label) | done
  deriving DecidableEq, Fintype

def slots : Fin 5 ↪ Fin 6 := ⟨![3, 1, 2, 4, 5], by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all⟩

def clampSlots : Fin 4 ↪ Fin 6 := ⟨![0, 2, 3, 4], by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all⟩

def program : Label → Stmt Symbol Label Local 5
  | .scan => clampCode 0 2 3 4 .scan .restore
  | .restore => transferCode 4 2 .restore (.decode .copyInput) (fun _ => true)
  | .decode (.decode .done) => clearCode 3 (.decode (.decode .done)) .done (fun _ => true)
  | .decode pc => embedCode slots Label.decode (CoordinateDecode.program pc)
  | .done => .halt

def registers (input : List Bool) (value bound : ℕ) : Fin 6 → List Symbol :=
  ![input.map some, unary value, unary bound, [], [], []]

/-- Reading a field implements the exact `Fin bound` codec on the prefix,
with polynomial space even for invalid binary values. -/
theorem read_bounded (answer : Bool) (bits : List Bool) (bound r : ℕ)
    (inputRoom : bits.length ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    ∃ value,
      Trace program r (localConfig .scan (carrying answer false) (registers bits 0 bound))
        (localConfig .done
          (carrying answer ((FixedWidthCodec.fin bound).decode (bits.take bound)).isSome)
          (registers (bits.drop bound) value bound)) ∧
      value ≤ bound ∧
      (∀ coordinate, (FixedWidthCodec.fin bound).decode (bits.take bound) = some coordinate →
        value = coordinate.val) := by
  have initial : ∀ j, (registers bits 0 bound j).length ≤ r := by
    intro j
    fin_cases j <;> simp [registers] <;> omega
  have extracted := clamp_prefix program clampSlots .scan .restore rfl
    .restore (.decode .copyInput) rfl rfl (carrying answer false)
    (registers bits 0 bound) rfl r initial (by simp [registers, clampSlots]; omega)
  let ready : Fin 6 → List Symbol :=
    ![(bits.drop bound).map some, [], unary bound, (bits.take bound).reverse.map some, [], []]
  have extractedMemory : replaceTwo (registers bits 0 bound) (clampSlots 0) (clampSlots 2)
      (((registers bits 0 bound) (clampSlots 0)).drop ((registers bits 0 bound) (clampSlots 1)).length)
      ((((registers bits 0 bound) (clampSlots 0)).take ((registers bits 0 bound) (clampSlots 1)).length).reverse ++
        (registers bits 0 bound) (clampSlots 2)) = ready := by
    funext j
    fin_cases j <;> simp [registers, clampSlots, ready, replaceTwo, Function.update_apply,
      List.map_reverse]
  rw [extractedMemory] at extracted
  obtain ⟨lastInput, value, decoded, valueBound, exactValue⟩ :=
    CoordinateDecode.decode_bounded answer (bits.take bound) bound r
      (by simp; omega) counterRoom
  have mapped := decoded.embed_active (by simp [localConfig]) slots Label.decode program
    (by
      intro pc nonhalt
      cases pc with
      | decode pc => cases pc <;> first | rfl | exact False.elim (nonhalt rfl)
      | _ => rfl)
    ready extracted.end_bound
  let finalMemory : Fin 6 → List Symbol :=
    ![(bits.drop bound).map some, unary value, unary bound, lastInput, [], []]
  have firstLayout : Function.extend slots
      (BoundedDecode.registers ((bits.take bound).reverse.map some) 0 bound) ready = ready := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside; rfl
  have lastLayout : Function.extend slots (BoundedDecode.registers lastInput value bound) ready = finalMemory := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside
      fin_cases j <;> simp_all [slots, Fin.exists_fin_succ, finalMemory, ready]
  simp only [embedConfig, localConfig, Option.map_some, firstLayout, lastLayout] at mapped
  have cleared := clear_all program 3 (.decode (.decode .done)) .done (fun _ => true) rfl
    (carrying answer ((FixedWidthCodec.fin bound).decode (bits.take bound)).isSome)
    finalMemory (by simp) r mapped.end_bound
  have clearedMemory : Function.update finalMemory (3 : Fin 6) [] = registers (bits.drop bound) value bound := by
    funext j
    fin_cases j <;> simp [finalMemory, registers, Function.update_apply]
  rw [clearedMemory] at cleared
  exact ⟨value, extracted.trans (mapped.trans cleared), valueBound, exactValue⟩

/-- In particular, an encoded coordinate is read successfully and leaves the
following configuration fields exactly unchanged. -/
theorem read_encoded (answer : Bool) (bound : ℕ) (coordinate : Fin bound)
    (suffix : List Bool) (r : ℕ) (inputRoom : bound + suffix.length ≤ r)
    (counterRoom : 2 * bound + 1 ≤ r) :
    Trace program r
      (localConfig .scan (carrying answer false)
        (registers ((FixedWidthCodec.fin bound).encode coordinate ++ suffix) 0 bound))
      (localConfig .done (carrying answer true) (registers suffix coordinate.val bound)) := by
  have width := (FixedWidthCodec.fin bound).encode_length coordinate
  change ((FixedWidthCodec.fin bound).encode coordinate).length = bound at width
  obtain ⟨value, trace, _, exactValue⟩ := read_bounded answer
    ((FixedWidthCodec.fin bound).encode coordinate ++ suffix) bound r
    (by simpa [List.length_append, width] using inputRoom) counterRoom
  have take : (((FixedWidthCodec.fin bound).encode coordinate ++ suffix).take bound) =
      (FixedWidthCodec.fin bound).encode coordinate := by exact List.take_left' width
  have drop : (((FixedWidthCodec.fin bound).encode coordinate ++ suffix).drop bound) = suffix := by
    exact List.drop_left' width
  have decoded := (FixedWidthCodec.fin bound).decode_encode coordinate
  have eqValue := exactValue coordinate (by rw [take]; exact decoded)
  simpa only [take, drop, decoded, Option.isSome_some, eqValue] using trace

end ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinate
