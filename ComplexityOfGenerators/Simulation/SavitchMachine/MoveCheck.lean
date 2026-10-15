import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateDecode

/-! Check a proposed head move using unary coordinates. Read-only heads clamp
at the ends; work heads instead reject a move outside the encoded window. The
same six-register routine implements both conventions. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.MoveCheck

open Turing StackSpace Frames
open BoundedDecode (unary)
set_option backward.isDefEq.respectTransparency false

inductive Label
  | start | validate (pc : BoundedDecode.Label) | compareStart | compare | clear | reject | done
  deriving DecidableEq, Fintype

def destination (move : Move) (clamp : Bool) (bound value : ℕ) : Option ℕ :=
  match move with
  | .left => if value = 0 ∧ clamp = false then none else some (value - 1)
  | .stay => some value
  | .right => if value < bound then some (value + 1) else if clamp then some value else none

def slots : Fin 5 ↪ Fin 6 := ⟨Fin.castSucc, Fin.castSucc_injective 5⟩

def program (move : Move) (clamp : Bool) : Label → Stmt Symbol Label Local 5
  | .start => match move with
      | .left => .peek 1 (fun v s => (v.1, s))
          (.branch (fun v => v.2.isSome)
            (.pop 1 (fun v _ => (v.1, none)) (.goto fun _ => .compareStart))
            (.load (fun v => (v.1, none)) (.goto fun _ => if clamp then .compareStart else .reject)))
      | .stay => .goto fun _ => .compareStart
      | .right => .goto fun _ => .validate .copyValue
  | .validate .done => .branch (fun v => v.1.returned.getD false)
      (.push 1 (fun _ => some false) (.goto fun _ => .compareStart))
      (.goto fun _ => if clamp then .compareStart else .reject)
  | .validate pc => embedCode slots Label.validate (BoundedDecode.program pc)
  | .compareStart => .load (fun v => ({v.1 with returned := some true}, none)) (.goto fun _ => .compare)
  | .compare => compareCode 1 5 .compare .clear
  | .clear => clearCode 5 .clear .done (fun _ => true)
  | .reject => .load (fun v => ({v.1 with returned := some false}, none)) (.goto fun _ => .done)
  | .done => .halt

def registers (value bound target : ℕ) : Fin 6 → List Symbol :=
  ![[], unary value, unary bound, [], [], unary target]

private theorem registers_bound (value bound target r : ℕ)
    (hv : value ≤ r) (hb : bound ≤ r) (ht : target ≤ r) :
    ∀ j, (registers value bound target j).length ≤ r := by
  intro j; fin_cases j <;> simp [registers] <;> assumption

private theorem compare_trace (move : Move) (clamp : Bool) (answer carry : Bool)
    (value bound target r : ℕ) (hv : value ≤ r) (hb : bound ≤ r) (ht : target ≤ r) :
    ∃ stk, Trace (program move clamp) r
      (localConfig .compareStart (carrying answer carry) (registers value bound target))
      (localConfig .done (carrying answer (decide (value = target))) stk) := by
  have initial := registers_bound value bound target r hv hb ht
  have compared := SavitchMachine.compare_trace (program move clamp) 1 5 (by decide)
    .compare .done .clear rfl rfl answer (registers value bound target) r initial
  have same : (registers value bound target 1 = registers value bound target 5) ↔ value = target := by
    constructor
    · intro h; simpa [registers] using congrArg List.length h
    · rintro rfl; rfl
  simp only [same] at compared
  exact ⟨_, .step initial (by simp [TM2.step, TM2.stepAux, localConfig, program, carrying]) compared⟩

private theorem reject_trace (move : Move) (clamp : Bool) (answer carry : Bool)
    (stk : Fin 6 → List Symbol) (r : ℕ) (bound : ∀ j, (stk j).length ≤ r) :
    Trace (program move clamp) r (localConfig .reject (carrying answer carry) stk)
      (localConfig .done (carrying answer false) stk) := by
  exact .step bound (by simp [TM2.step, TM2.stepAux, localConfig, program, carrying]) (.refl _ bound)

private theorem validate_trace (move : Move) (clamp : Bool) (answer : Bool)
    (value bound target r : ℕ) (hv : value ≤ bound) (hb : bound ≤ r) (ht : target ≤ r) :
    Trace (program move clamp) r
      (localConfig (.validate .copyValue) (carrying answer false) (registers value bound target))
      (localConfig (.validate .done) (carrying answer (decide (value < bound))) (registers value bound target)) := by
  let background := registers value bound target
  have trace := (BoundedDecode.validate answer value bound r hv hb).embed_active
    (by simp [localConfig]) slots Label.validate (program move clamp)
    (by intro q nonhalt; cases q <;> first | rfl | exact False.elim (nonhalt rfl))
    background (registers_bound value bound target r (hv.trans hb) hb ht)
  have layout : Function.extend slots (BoundedDecode.registers [] value bound) background = background := by
    apply extend_eq
    · intro i; fin_cases i <;> rfl
    · intro j outside; rfl
  simpa only [embedConfig, localConfig, Option.map_some, layout] using trace

/-- Exact finite-control head-movement test. Both supplied coordinates are
bounded; invalid binary fields are rejected by the preceding coordinate parser. -/
theorem run (move : Move) (clamp : Bool) (answer : Bool) (value bound target r : ℕ)
    (hv : value ≤ bound) (hb : bound ≤ r) (ht : target ≤ r) :
    ∃ stk, Trace (program move clamp) r
      (localConfig .start (carrying answer false) (registers value bound target))
      (localConfig .done (carrying answer (decide (destination move clamp bound value = some target))) stk) := by
  have initial := registers_bound value bound target r (hv.trans hb) hb ht
  cases move with
  | stay =>
      obtain ⟨stk, tail⟩ := compare_trace .stay clamp answer false value bound target r (hv.trans hb) hb ht
      refine ⟨stk, ?_⟩
      simpa [destination] using Trace.step (show Within r (localConfig .start (carrying answer false)
        (registers value bound target)) from initial)
        (show TM2.step (program .stay clamp) (localConfig .start (carrying answer false)
          (registers value bound target)) = some (localConfig .compareStart (carrying answer false)
          (registers value bound target)) from rfl) tail
  | left =>
      cases value with
      | zero =>
          cases clamp with
          | false =>
              refine ⟨registers 0 bound target, ?_⟩
              simpa [destination] using Trace.step
                (show Within r (localConfig .start (carrying answer false) (registers 0 bound target)) from initial)
                (show TM2.step (program .left false) (localConfig .start (carrying answer false) (registers 0 bound target)) =
                  some (localConfig .reject (carrying answer false) (registers 0 bound target)) by
                    simp [TM2.step, TM2.stepAux, localConfig, program, registers])
                (reject_trace .left false answer false _ r initial)
          | true =>
              obtain ⟨stk, tail⟩ := compare_trace .left true answer false 0 bound target r (by omega) hb ht
              refine ⟨stk, ?_⟩
              simpa [destination] using Trace.step
                (show Within r (localConfig .start (carrying answer false) (registers 0 bound target)) from initial)
                (show TM2.step (program .left true) (localConfig .start (carrying answer false) (registers 0 bound target)) =
                  some (localConfig .compareStart (carrying answer false) (registers 0 bound target)) by
                    simp [TM2.step, TM2.stepAux, localConfig, program, registers]) tail
      | succ value =>
          obtain ⟨stk, tail⟩ := compare_trace .left clamp answer false value bound target r (by omega) hb ht
          refine ⟨stk, ?_⟩
          have step : TM2.step (program .left clamp) (localConfig .start (carrying answer false) (registers (value + 1) bound target)) =
              some (localConfig .compareStart (carrying answer false) (registers value bound target)) := by
            simp [TM2.step, TM2.stepAux, localConfig, program, registers, List.replicate_succ]
            funext j; fin_cases j <;> simp
          simpa [destination] using Trace.step
            (show Within r (localConfig .start (carrying answer false) (registers (value + 1) bound target)) from initial) step tail
  | right =>
      have validated := validate_trace .right clamp answer value bound target r hv hb ht
      have first := Trace.step
        (show Within r (localConfig .start (carrying answer false) (registers value bound target)) from initial)
        (show TM2.step (program .right clamp) (localConfig .start (carrying answer false) (registers value bound target)) =
          some (localConfig (.validate .copyValue) (carrying answer false) (registers value bound target)) from rfl) validated
      by_cases room : value < bound
      · simp only [room, decide_true] at first
        obtain ⟨stk, tail⟩ := compare_trace .right clamp answer true (value + 1) bound target r (by omega) hb ht
        have step : TM2.step (program .right clamp) (localConfig (.validate .done) (carrying answer true) (registers value bound target)) =
            some (localConfig .compareStart (carrying answer true) (registers (value + 1) bound target)) := by
          simp [TM2.step, TM2.stepAux, localConfig, program, registers, carrying, List.replicate_succ]
          funext j; fin_cases j <;> simp
        refine ⟨stk, ?_⟩
        simpa [destination, room] using first.trans (.step first.end_bound step tail)
      · simp only [room, decide_false] at first
        cases clamp with
        | false =>
            refine ⟨registers value bound target, ?_⟩
            have step : TM2.step (program .right false) (localConfig (.validate .done) (carrying answer false) (registers value bound target)) =
                some (localConfig .reject (carrying answer false) (registers value bound target)) := rfl
            simpa [destination, room] using first.trans (.step first.end_bound step
              (reject_trace .right false answer false _ r initial))
        | true =>
            obtain ⟨stk, tail⟩ := compare_trace .right true answer false value bound target r (hv.trans hb) hb ht
            have step : TM2.step (program .right true) (localConfig (.validate .done) (carrying answer false) (registers value bound target)) =
                some (localConfig .compareStart (carrying answer false) (registers value bound target)) := rfl
            refine ⟨stk, ?_⟩
            simpa [destination, room] using first.trans (.step first.end_bound step tail)

theorem destination_clamped (move : Move) (bound value : ℕ) (valid : value ≤ bound) :
    destination move true bound value = some (move.onInput bound value) := by
  cases move <;> simp only [destination, Move.onInput]
  · simp
  · rw [Nat.min_eq_left valid]
  · split_ifs with room
    · rw [Nat.min_eq_left (by omega)]
    · have eq : value = bound := by omega
      simp [eq]

/-- Strict movement is ordinary integer movement, with no clamping at the
work-window endpoints. Offsetting both coordinates by the window origin does
not change this relation. -/
theorem destination_strict (move : Move) (bound value target : ℕ)
    (valid : value ≤ bound) (targetValid : target ≤ bound) :
    destination move false bound value = some target ↔ move.onInt (value : ℤ) = (target : ℤ) := by
  cases move <;> simp only [destination, Move.onInt]
  · split_ifs with atZero
    · simp only [and_true] at atZero
      simp [atZero]
    · simp only [and_true] at atZero
      simp only [Option.some.injEq]
      omega
  · simp
  · by_cases room : value < bound <;> simp [room] <;> omega


end ComplexityOfGenerators.Simulation.SavitchMachine.MoveCheck
