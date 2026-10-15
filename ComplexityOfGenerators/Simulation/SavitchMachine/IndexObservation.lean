import ComplexityOfGenerators.Simulation.SavitchMachine.ReadCoordinateAt

/-! Check whether an encoded unary-index head sees a marker or the right
blank cell. The index tape has the original word length; its coordinate codec
also admits the blank cell at that length. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.IndexObservation

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [Inhabited S]

inductive Label
  | read (pc : ReadCoordinateAt.Label) | prepare | validate (pc : BoundedDecode.Label) | reject | done
  deriving DecidableEq, Fintype

def slots : Fin 5 ↪ Fin 7 := ⟨![3, 0, 2, 4, 5], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

def program (write : Symbol → S) (read : S → Symbol) (states : ℕ) (expected : Bool) :
    Label → Stmt S Label (Status × Option S) 6
  | .read .done => .branch (fun v => v.1.returned.getD false)
      (.goto fun _ => .prepare) (.goto fun _ => .reject)
  | .read pc => embedCode (Function.Embedding.refl _) Label.read (ReadCoordinateAt.program write read 1 (states + 2) pc)
  | .prepare => .pop 2 (fun v _ => ({v.1 with returned := some false}, none)) (.goto fun _ => .validate .copyValue)
  | .validate .done => .load (fun v =>
      ({v.1 with returned := some (decide (v.1.returned.getD false = expected))}, none)) (.goto fun _ => .done)
  | .validate pc => embedCode slots Label.validate
      (transportCode write read (Initialize.pack write) (Initialize.unpack read) (BoundedDecode.program pc))
  | .reject => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)
  | .done => .halt

/-- Exact uniform index-observation check; invalid coordinate fields reject
regardless of which observation is requested. -/
theorem run (write : Symbol → S) (read : S → Symbol) (inverse : Function.LeftInverse read write)
    (states : ℕ) (expected answer : Bool) (bits : List Bool) (input : List S) (r : ℕ)
    (bitsRoom : bits.length ≤ r) (inputRoom : input.length ≤ r)
    (offsetRoom : input.length + (states + 2) ≤ r)
    (counterRoom : 2 * (input.length + 1) + 1 ≤ r) :
    ∃ stk,
      Trace (program write read states expected) r
        (localConfig (.read (.skip .copy)) (carrying answer false)
          (ReadCoordinateAt.before write bits [] (input.length + 1) input))
        (localConfig .done (carrying answer
          (((FixedWidthCodec.fin (input.length + 1)).decode
            ((bits.drop (input.length + (states + 2))).take (input.length + 1))).any
              (fun head => decide (decide (head.val < input.length) = expected)))) stk) ∧ stk 6 = input := by
  let P := program write read states expected
  let field := (bits.drop (input.length + (states + 2))).take (input.length + 1)
  obtain ⟨value, parsed, valueBound, exactValue⟩ := ReadCoordinateAt.run write read inverse 1 (states + 2)
    answer bits [] input (input.length + 1) r bitsRoom (by simp) inputRoom (by simpa using offsetRoom) counterRoom
  simp only [Nat.one_mul] at parsed exactValue
  have first := parsed.rename_active (by simp [localConfig]) Label.read P (by
    intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
  simp only [renameConfig, localConfig, Option.map_some] at first
  let parsedMemory := ReadCoordinateAt.after write value [] (input.length + 1) input
  change Trace P r _ (localConfig (.read .done)
    (carrying answer ((FixedWidthCodec.fin (input.length + 1)).decode field).isSome) parsedMemory) at first
  cases decoded : (FixedWidthCodec.fin (input.length + 1)).decode field with
  | none =>
      simp only [decoded, Option.isSome_none] at first
      refine ⟨parsedMemory, ?_, rfl⟩
      simp only [Option.any_none]
      exact first.trans (.step first.end_bound rfl
        (.step first.end_bound (by simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying]) (.refl _ first.end_bound)))
  | some head =>
      have valueEq := exactValue head decoded
      subst value
      simp only [decoded, Option.isSome_some] at first
      have ready : TM2.step P (localConfig (.read .done) (carrying answer true) parsedMemory) =
          some (localConfig .prepare (carrying answer true) parsedMemory) := rfl
      let prepared := ReadCoordinateAt.after write head.val [] input.length input
      have prepare : TM2.step P (localConfig .prepare (carrying answer true) parsedMemory) =
          some (localConfig (.validate .copyValue) (carrying answer false) prepared) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying,
          parsedMemory, prepared, ReadCoordinateAt.after, List.replicate_succ]
        funext j; fin_cases j <;> simp
      have preparedBound : ∀ j, (prepared j).length ≤ r := by
        intro j; fin_cases j <;> simp [prepared, ReadCoordinateAt.after] <;> omega
      have checked := BoundedDecode.validate answer head.val input.length r (by omega) inputRoom
      have transported := Trace.transport write read (Initialize.pack write) (Initialize.unpack read)
        inverse (Initialize.pack_inverse write read inverse) checked
      have mapped := transported.embed_active (by simp [transportConfig, localConfig]) slots Label.validate P
        (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl)) prepared preparedBound
      have layout : Function.extend slots
          (fun j => (BoundedDecode.registers [] head.val input.length j).map write) prepared = prepared := by
        apply extend_eq
        · intro i; fin_cases i <;> rfl
        · intro j outside; rfl
      simp only [embedConfig, transportConfig, localConfig, Initialize.pack,
        Option.map_some, Option.map_none, layout] at mapped
      have finish : TM2.step P
          (localConfig (.validate .done) (carrying answer (decide (head.val < input.length))) prepared) =
          some (localConfig .done (carrying answer (decide (decide (head.val < input.length) = expected))) prepared) := by
        simp [P, program, TM2.step, TM2.stepAux, localConfig, carrying]
      refine ⟨prepared, ?_, rfl⟩
      simp only [Option.any_some]
      exact first.trans (.step first.end_bound ready (.step first.end_bound prepare
        (mapped.trans (.step mapped.end_bound finish (.refl _ mapped.end_bound)))))

end ComplexityOfGenerators.Simulation.SavitchMachine.IndexObservation
