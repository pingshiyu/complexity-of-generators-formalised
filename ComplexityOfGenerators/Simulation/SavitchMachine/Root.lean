import ComplexityOfGenerators.Simulation.SavitchMachine.FrameStore
import ComplexityOfGenerators.Simulation.SavitchMachine.ReturnTrue
import ComplexityOfGenerators.Simulation.StackSpace.Copy
import ComplexityOfGenerators.Simulation.StackSpace.MapTransfer

/-! Assemble the initial Savitch frame from its unary depth and encoded
initial vertex. The two zero vertex fields are made by scanning a copy of the
initial code, so the program does not need its width in finite control. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Root

open Turing StackSpace Frames Complexity
set_option backward.isDefEq.respectTransparency false

inductive Label
  | seed | copy | duplicate | zero | duplicateZeros
  | mark (field : Fin 6) | store (field : Fin 6) | done
  deriving DecidableEq, Fintype

def phase : ℕ → Label
  | 0 => .done
  | n + 1 => if h : n < 6 then .mark ⟨n, h⟩ else .done

def program : Label → Stmt Symbol Label Local 11
  | .seed => .push 6 (fun _ => some true) (.push 7 (fun _ => some false) (.goto fun _ => .copy))
  | .copy => transferCode 9 0 .copy .duplicate (fun _ => true)
  | .duplicate => duplicateCode 0 9 10 .duplicate .zero
  | .zero => mapTransferCode 10 0 .zero .duplicateZeros (fun _ => some false)
  | .duplicateZeros => duplicateCode 0 10 11 .duplicateZeros (phase 6)
  | .mark j => .push (src j) (fun _ => none) (.goto fun _ => .store j)
  | .store j => transferCode (dst j) (src j) (.store j) (phase j.val) (fun _ => true)
  | .done => .halt

def frame (depth : ℕ) (code : List Bool) : Sav.Frm :=
  ⟨true, false, List.replicate depth false, code,
    List.replicate code.length false, List.replicate code.length false⟩

def prepared (depth : ℕ) (code : List Bool) : Memory :=
  ![[], [], [], [], [], [], [], [], List.replicate depth (some false), code.reverse.map some, [], []]

theorem frame_bound (depth : ℕ) (code : List Bool) :
    ∀ j, (column [frame depth code] j).length ≤ depth + code.length + 2 := by
  intro j
  fin_cases j <;> simp [column, field, frame] <;> omega

/-- This is a concrete prefix of the interpreter, ending with exactly one
root frame and six empty cache registers. The suspended-frame columns are
created by the same verified store routine used elsewhere. -/
theorem assemble (depth : ℕ) (code : List Bool) :
    Trace program (depth + code.length + 2)
      (localConfig .seed (status ⟨false, false, none, []⟩) (prepared depth code))
      (localConfig .done (status ⟨false, false, none, []⟩)
        (memory [frame depth code] (fun _ => []))) := by
  let r := depth + code.length + 2
  let v := status ⟨false, false, none, []⟩
  let seeded : Memory :=
    ![[], [], [], [], [], [], [some true], [some false],
      List.replicate depth (some false), code.reverse.map some, [], []]
  have initial : ∀ j, (prepared depth code j).length ≤ r := by
    intro j
    fin_cases j <;> simp [prepared, r] <;> omega
  have seedBound : ∀ j, (seeded j).length ≤ r := by
    intro j
    fin_cases j <;> simp [seeded, r] <;> omega
  have seed : TM2.step program (localConfig .seed v (prepared depth code)) =
      some (localConfig .copy v seeded) := by
    simp [program, TM2.step, localConfig, TM2.stepAux, prepared, seeded]
    funext j
    fin_cases j <;> simp [Function.update_apply]
  have copy := copy_all program 0 9 10 .duplicate .zero .copy rfl rfl
    (by decide) (by decide) (by decide) v seeded rfl r seedBound (by simp [seeded, r] <;> omega)
  let copied : Memory :=
    ![[], [], [], [], [], [], [some true], [some false],
      List.replicate depth (some false), code.reverse.map some, code.reverse.map some, []]
  have copyMemory : Function.update seeded (10 : Fin 12) (seeded 9 ++ seeded 10) = copied := by
    funext j
    fin_cases j <;> simp [seeded, copied, Function.update_apply]
  rw [copyMemory] at copy
  have zero := mapTransfer_all program 10 0 (by decide) .zero .duplicateZeros (fun _ => some false) rfl
    v copied r copy.end_bound (by simp [copied, r] <;> omega)
  let mapped : Memory :=
    ![List.replicate code.length (some false), [], [], [], [], [], [some true], [some false],
      List.replicate depth (some false), code.reverse.map some, [], []]
  have zeroMemory : replaceTwo copied (10 : Fin 12) 0 []
      ((copied 10).reverse.map (fun _ => some false) ++ copied 0) = mapped := by
    funext j
    fin_cases j <;> simp [copied, mapped, replaceTwo, Function.update_apply, Function.comp_def, List.map_const']
  rw [zeroMemory] at zero
  have zeros := duplicate_all program 0 10 11 (by decide) (by decide) (by decide)
    .duplicateZeros (phase 6) rfl v mapped r zero.end_bound
    (by simp [mapped, r] <;> omega) (by simp [mapped, r] <;> omega)
  have ready : replaceThree mapped (0 : Fin 12) 10 11 []
      ((mapped 0).reverse ++ mapped 10) ((mapped 0).reverse ++ mapped 11) =
      memory [] (fun j => (field (frame depth code) j).reverse) := by
    funext j
    fin_cases j <;>
      simp [mapped, replaceThree, replaceTwo, Function.update_apply, memory, field, frame,
        Fin.addCases, Fin.castLT, Fin.subNat]
  rw [ready] at zeros
  have stored := store_frame program phase Label.store
    (fun j => by simp only [phase, j.isLt, ↓reduceDIte, program])
    (fun _ => rfl) v (frame depth code) [] r (frame_bound depth code)
  exact .step initial seed (copy.trans (zero.trans (zeros.trans stored)))

/-- The assembled frame is the root used in the proved graph-search theorem. -/
theorem frame_eq_root {V : Type} (codec : FixedWidthCodec V) (depth : ℕ) (start : V) :
    frame depth (codec.encode start) = SavitchStack.root codec depth start := by
  simp [frame, SavitchStack.root, SavitchStack.zeroCode, codec.encode_length]

end ComplexityOfGenerators.Simulation.SavitchMachine.Root
