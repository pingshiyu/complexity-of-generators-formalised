import ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt
import ComplexityOfGenerators.Simulation.SavitchMachine.MoveCheck

/-! Compose field location, bounded decoding and native head-movement checking.
The source coordinate is preserved while the target field is decoded. Invalid
target fields reject before movement; the persistent input is never changed. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.HeadComparison

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

variable {S : Type} [Inhabited S]

inductive Label
  | read (pc : ReadCoordinateAt.Label) | transfer | prepare
  | move (pc : MoveCheck.Label) | reject | done
  deriving DecidableEq, Fintype

def slots : Fin 6 ↪ Fin 7 := ⟨Fin.castSucc, Fin.castSucc_injective 6⟩

def program (write : Symbol → S) (read : S → Symbol) (a b : ℕ) (direction : Move) (clamp : Bool) :
    Label → Stmt S Label (Status × Option S) 6
  | .read .done => .branch (fun v => v.1.returned.getD false)
      (.goto fun _ => .transfer) (.goto fun _ => .reject)
  | .read pc => embedCode (Function.Embedding.refl _) Label.read (ReadCoordinateAt.program write read a b pc)
  | .transfer => transferCode 0 5 .transfer .prepare (fun _ => true)
  | .prepare => .pop 2 (fun v _ => ({v.1 with returned := some false}, none)) (.goto fun _ => .move .start)
  | .move .done => .goto fun _ => .done
  | .move pc => embedCode slots Label.move
      (transportCode write read (Initialize.pack write) (Initialize.unpack read) (MoveCheck.program direction clamp pc))
  | .reject => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)
  | .done => .halt

/-- Exact native comparison against a selected target field. No assumption
that the target configuration or coordinate is valid is made. -/
theorem run (write : Symbol → S) (read : S → Symbol) (inverse : Function.LeftInverse read write)
    (a b : ℕ) (direction : Move) (clamp answer : Bool)
    (bits : List Bool) (input : List S) (first bound r : ℕ)
    (firstValid : first < bound) (bitsRoom : bits.length ≤ r) (inputRoom : input.length ≤ r)
    (offsetRoom : a * input.length + b ≤ r) (counterRoom : 2 * bound + 1 ≤ r) :
    ∃ stk, Trace (program write read a b direction clamp) r
      (localConfig (.read (.skip .copy)) (carrying answer false)
        (ReadCoordinateAt.before write bits ((unary first).map write) bound input))
      (localConfig .done
        (carrying answer (((FixedWidthCodec.fin bound).decode
          ((bits.drop (a * input.length + b)).take bound)).any fun target =>
            decide (MoveCheck.destination direction clamp (bound - 1) first = some target.val))) stk) ∧ stk 6 = input := by
  let P := program write read a b direction clamp
  let field := (bits.drop (a * input.length + b)).take bound
  obtain ⟨value, parsed, valueBound, exactValue⟩ := ReadCoordinateAt.run write read inverse a b answer bits
    ((unary first).map write) input bound r bitsRoom (by simp; omega) inputRoom offsetRoom counterRoom
  have firstTrace := parsed.rename_active (by simp [localConfig]) Label.read P (by
    intro q nonhalt
    cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, localConfig, Option.map_some] at firstTrace
  let parsedMemory := ReadCoordinateAt.after write value ((unary first).map write) bound input
  change Trace P r
    (localConfig (.read (.skip .copy)) (carrying answer false)
      (ReadCoordinateAt.before write bits ((unary first).map write) bound input))
    (localConfig (.read .done) (carrying answer ((FixedWidthCodec.fin bound).decode field).isSome) parsedMemory) at firstTrace
  cases decoded : (FixedWidthCodec.fin bound).decode field with
  | none =>
      simp only [decoded, Option.isSome_none] at firstTrace
      have rejected : TM2.step P (localConfig (.read .done) (carrying answer false) parsedMemory) =
          some (localConfig .reject (carrying answer false) parsedMemory) := rfl
      have finish : TM2.step P (localConfig .reject (carrying answer false) parsedMemory) =
          some (localConfig .done (carrying answer false) parsedMemory) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying]
      refine ⟨parsedMemory, ?_, rfl⟩
      simp only [Option.any_none]
      exact firstTrace.trans (.step firstTrace.end_bound rejected
        (.step firstTrace.end_bound finish (.refl _ firstTrace.end_bound)))
  | some target =>
      have valueEq := exactValue target decoded
      subst value
      simp only [decoded, Option.isSome_some] at firstTrace
      have ready : TM2.step P (localConfig (.read .done) (carrying answer true) parsedMemory) =
          some (localConfig .transfer (carrying answer true) parsedMemory) := rfl
      have transferred := transfer_all P 0 5 (by decide) .transfer .prepare (fun _ => true) rfl
        (carrying answer true) parsedMemory (by simp) r firstTrace.end_bound (by
          simp [parsedMemory, ReadCoordinateAt.after]; omega)
      let withTarget : Fin 7 → List S :=
        ![[], (unary first).map write, (unary bound).map write, [], [], (unary target.val).map write, input]
      have transferLayout : replaceTwo parsedMemory (0 : Fin 7) 5 []
          ((parsedMemory 0).reverse ++ parsedMemory 5) = withTarget := by
        funext j; fin_cases j <;> simp [parsedMemory, ReadCoordinateAt.after, withTarget, replaceTwo, List.map_reverse]
      rw [transferLayout] at transferred
      let prepared : Fin 7 → List S :=
        ![[], (unary first).map write, (unary (bound - 1)).map write, [], [], (unary target.val).map write, input]
      have prepare : TM2.step P (localConfig .prepare (carrying answer true) withTarget) =
          some (localConfig (.move .start) (carrying answer false) prepared) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying, withTarget, prepared]
        funext j; fin_cases j <;> simp [List.map_tail, List.tail_replicate]
      have preparedBound : ∀ j, (prepared j).length ≤ r := by
        intro j; fin_cases j <;> simp [prepared] <;> omega
      obtain ⟨lastMemory, moved⟩ := MoveCheck.run direction clamp answer first (bound - 1) target.val r
        (by omega) (by omega) (by omega)
      have transported := Trace.transport write read (Initialize.pack write) (Initialize.unpack read)
        inverse (Initialize.pack_inverse write read inverse) moved
      have mapped := transported.embed_active (by simp [transportConfig, localConfig]) slots Label.move P
        (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) prepared preparedBound
      have firstLayout : Function.extend slots
          (fun j => (MoveCheck.registers first (bound - 1) target.val j).map write) prepared = prepared := by
        apply extend_eq
        · intro i; fin_cases i <;> rfl
        · intro j outside; rfl
      simp only [embedConfig, transportConfig, localConfig, Initialize.pack,
        Option.map_some, Option.map_none, firstLayout] at mapped
      let finalMemory := Function.extend slots (fun j => (lastMemory j).map write) prepared
      have finish : TM2.step P (localConfig (.move .done)
          (carrying answer (decide (MoveCheck.destination direction clamp (bound - 1) first = some target.val))) finalMemory) =
          some (localConfig .done
            (carrying answer (decide (MoveCheck.destination direction clamp (bound - 1) first = some target.val))) finalMemory) := rfl
      have inputPreserved : finalMemory 6 = input := by
        have outside : ¬ ∃ i, slots i = (6 : Fin 7) := by
          rintro ⟨i, h⟩
          have eq := congrArg Fin.val h
          have lt := i.isLt
          simp only [slots, Function.Embedding.coeFn_mk, Fin.coe_castSucc, Fin.reduceFinMk] at eq
          omega
        rw [show finalMemory 6 = prepared 6 from Function.extend_apply' _ _ _ outside]
        rfl
      refine ⟨finalMemory, ?_, inputPreserved⟩
      simp only [Option.any_some]
      exact firstTrace.trans (.step firstTrace.end_bound ready
        (transferred.trans (.step transferred.end_bound prepare
          (mapped.trans (.step mapped.end_bound finish (.refl _ mapped.end_bound))))))

end ComplexityOfGenerators.Simulation.SavitchMachine.HeadComparison
