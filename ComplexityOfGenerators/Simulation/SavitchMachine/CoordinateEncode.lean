import ComplexityOfGenerators.Simulation.SavitchMachine.FieldCounter
import ComplexityOfGenerators.Simulation.StackSpace.Copy

/-! Build a fixed-width configuration coordinate from unary value and width
registers. This supplies the work-head offset in the initial configuration;
the bound and all counter arithmetic live on stacks, not in finite control. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateEncode

open Turing StackSpace Frames Complexity
set_option backward.isDefEq.respectTransparency false

inductive Label
  | seed | copyWidth | duplicateWidth | check | count | restore | done
  deriving DecidableEq, Fintype

abbrev unary (n : ℕ) : List Symbol := List.replicate n (some false)

def program : Label → Stmt Symbol Label Local 3
  | .seed => .push 2 (fun _ => none) (.goto fun _ => .copyWidth)
  | .copyWidth => transferCode 1 3 .copyWidth .duplicateWidth (fun _ => true)
  | .duplicateWidth => duplicateCode 3 1 2 .duplicateWidth .check
  | .check => .pop 0 (fun v s => (v.1, s))
      (.branch (fun v => v.2.isSome)
        (.load (fun v => ({v.1 with returned := some true}, none)) (.goto fun _ => .count))
        (.load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)))
  | .count => fieldCounterCode 2 3 .count .restore
  | .restore => transferCode 3 2 .restore .check (fun _ => true)
  | .done => .halt

def registers (remaining width : ℕ) (bits : List Bool) : Fin 4 → List Symbol :=
  ![unary remaining, unary width, bits.map some ++ [none], []]

theorem registers_bound (remaining width : ℕ) (bits : List Bool) (r : ℕ)
    (hr : remaining ≤ r) (hw : width ≤ r) (hb : bits.length + 1 ≤ r) :
    ∀ j, (registers remaining width bits j).length ≤ r := by
  intro j
  fin_cases j <;> simpa [registers] using (by assumption : _)

/-- The number of iterations is stored in unary, and each increment is the
previously verified fixed-width counter. The preserved width register is
charged throughout the run. -/
theorem count (answer carry : Bool) (remaining width : ℕ) (bits : List Bool) (r : ℕ)
    (hr : remaining ≤ r) (hw : width ≤ r) (hb : bits.length + 1 ≤ r) :
    Trace program r (localConfig .check (carrying answer carry) (registers remaining width bits))
      (localConfig .done (carrying answer false) (registers 0 width (bumpBits^[remaining] bits))) := by
  induction remaining generalizing bits carry with
  | zero =>
      have initial := registers_bound 0 width bits r hr hw hb
      have next : TM2.step program (localConfig .check (carrying answer carry) (registers 0 width bits)) =
          some (localConfig .done (carrying answer false) (registers 0 width bits)) := by
        simp [program, TM2.step, localConfig, TM2.stepAux, carrying, registers]
      exact .step initial next (.refl _ initial)
  | succ n ih =>
      have initial := registers_bound (n + 1) width bits r hr hw hb
      have next : TM2.step program (localConfig .check (carrying answer carry) (registers (n + 1) width bits)) =
          some (localConfig .count (carrying answer true) (registers n width bits)) := by
        simp [program, TM2.step, localConfig, TM2.stepAux, carrying, registers, List.replicate_succ]
        funext j
        fin_cases j <;> simp [Function.update_apply]
      have increment := fieldCounter_trace program 2 3 (by decide) .count .restore .check rfl rfl
        answer true (registers n width bits) bits [] rfl rfl r
        (registers_bound n width bits r (by omega) hw hb)
      have finish : Function.update (registers n width bits) (2 : Fin 4)
          ((addBit true bits).2.map some ++ [none]) = registers n width (bumpBits bits) := by
        funext j
        fin_cases j <;> simp [registers, bumpBits, Function.update_apply]
      rw [finish] at increment
      have tail := ih (bumpOver bits) (bumpBits bits) (by omega) (by simpa using hb)
      simpa only [Function.iterate_succ_apply] using
        Trace.step (show Within r (localConfig .check (carrying answer carry) (registers (n + 1) width bits)) from initial)
          next (increment.trans tail)

theorem zero_bits (width : ℕ) : bitsOfLenLE width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [bitsOfLenLE, ih, List.replicate_succ]

/-- The completed encoder starts with two unary registers and empty output
and scratch registers. It preserves the width, consumes the value, and writes
the exact binary field used by `FixedWidthCodec.fin`, followed by a delimiter. -/
theorem encode (answer : Bool) (value width : ℕ) (fits : value < 2 ^ width) :
    Trace program (value + width + 1)
      (localConfig .seed (carrying answer false) ![unary value, unary width, [], []])
      (localConfig .done (carrying answer false) (registers 0 width (bitsOfLenLE width value))) := by
  let r := value + width + 1
  let original : Fin 4 → List Symbol := ![unary value, unary width, [], []]
  let prepared : Fin 4 → List Symbol := ![unary value, unary width, [none], []]
  have initial : ∀ j, (original j).length ≤ r := by
    intro j
    fin_cases j <;> simp [original, r] <;> omega
  have preparedBound : ∀ j, (prepared j).length ≤ r := by
    intro j
    fin_cases j <;> simp [prepared, r] <;> omega
  have seed : TM2.step program (localConfig .seed (carrying answer false) original) =
      some (localConfig .copyWidth (carrying answer false) prepared) := by
    simp [program, TM2.step, localConfig, TM2.stepAux, original, prepared]
    funext j
    fin_cases j <;> simp [Function.update_apply]
  have copy := copy_all program 3 1 2 .duplicateWidth .check .copyWidth rfl rfl
    (by decide) (by decide) (by decide) (carrying answer false) prepared rfl r preparedBound (by
      simp [prepared, r] <;> omega)
  have memory : Function.update prepared (2 : Fin 4) (prepared 1 ++ prepared 2) =
      registers value width (bitsOfLenLE width 0) := by
    funext j
    fin_cases j <;> simp [prepared, registers, zero_bits, Function.update_apply]
  rw [memory] at copy
  have tail := count answer false value width (bitsOfLenLE width 0) r (by dsimp [r] <;> omega)
    (by dsimp [r] <;> omega) (by simp [r] <;> omega)
  rw [bumpBits_iterate width value fits] at tail
  exact .step initial seed (copy.trans tail)

end ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateEncode
