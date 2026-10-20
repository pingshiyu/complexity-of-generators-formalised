import ComplexityOfGenerators.Simulation.NativeNTM.Tape
import Mathlib.Data.Fintype.Sum

/-! A finite library NTM for a native decision machine with empty auxiliary
input and unary index equal to the word length. Binary input uses bounded unary
letter codes. The input and index are loaded onto charged work tracks. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)
local instance programAlphabetDecEq : DecidableEq α := Classical.decEq α

inductive Track (α : Type) (s : ℕ)
  | input (symbol : Option α)
  | index (origin : Bool)
  | work (symbol : Option (Bool × Fin s))
  deriving Fintype, DecidableEq

inductive Phase (q : Type) (a : ℕ)
  | boot | mark | load (count : Fin (a + 1)) | rewind
  | simulate (state : q) (negative : Bool)
  | halt
  deriving Fintype, DecidableEq

abbrev Tracks := Track α M.symbols
abbrev State := Phase (Fin M.states) (Fintype.card α)
abbrev trackEquiv := Fintype.equivFin (Tracks M)

def writable : Γ → Γw
  | .zero => .zero | .one => .one | .blank | .start => .blank

@[simp] theorem writable_toΓ (a : Γw) : writable a.toΓ = a := by cases a <;> rfl

structure Action (Q T : Type) where
  state : Q
  write : T → Γw
  output : Γw := .blank
  inputDir : Dir3 := .stay
  workDir : T → Dir3 := fun _ => .stay

/-- Marker-safe movement makes the transition table legal even on unreachable
combinations of tape symbols. -/
def safeDir (symbol : Γ) (direction : Dir3) : Dir3 :=
  if symbol = .start then .right else direction

@[simp] theorem safeDir_toΓ (a : Γw) (d : Dir3) : safeDir a.toΓ d = d := by
  cases a <;> simp [safeDir, Γw.toΓ]

@[simp] theorem safeDir_zero (d : Dir3) : safeDir .zero d = d := rfl
@[simp] theorem safeDir_one (d : Dir3) : safeDir .one d = d := rfl
@[simp] theorem safeDir_blank (d : Dir3) : safeDir .blank d = d := rfl
@[simp] theorem tape_move_stay (t : Tape) : t.move .stay = t := rfl

def core (bit : Bool) (state : State M) (input : Γ) (read : Tracks M → Γ) :
    Action (State M) (Tracks M) :=
  let keep := fun t => writable (read t)
  let go := fun q => ({state := q, write := keep} : Action (State M) (Tracks M))
  let reject := {go .halt with output := .zero}
  match state with
  | .boot => go .mark
  | .mark => {go (.load 0) with write := fun
      | .input none | .index true | .work none => .one
      | _ => .blank}
  | .load count =>
    match input with
    | .zero => if h : count.val < Fintype.card α then
        {go (.load ⟨count.val + 1, by omega⟩) with inputDir := .right}
      else reject
    | .one => if h : count.val < Fintype.card α then
        let letter := (Fintype.equivFin α).symm ⟨count.val, h⟩
        {go (.load 0) with
          inputDir := .right
          write := (fun
            | .input (some a) => if a = letter then .one else .blank
            | .index false => .one
            | t => keep t)
          workDir := fun | .input _ | .index _ => .right | _ => .stay}
      else reject
    | .blank => if count.val = 0 then go .rewind else reject
    | .start => reject
  | .rewind =>
      if read (.input none) = .one then go (.simulate M.initial false)
      else {go .rewind with workDir := fun | .input _ | .index _ => .left | _ => .stay}
  | .simulate q negative =>
      let inputLetter := decodeTracks (fun a => read (.input (some a)))
      let origin := decide (read (.work none) = .one)
      let cell := decodeTracks (fun a => read (.work (some (negative, a))))
      match M.transition q inputLetter none
          (if read (.index false) = .one then some () else none) cell with
      | .accept => {go .halt with output := .one}
      | .reject => reject
      | .readRandom no yes => go (.simulate (if bit then yes else no) negative)
      | .step next write work input _ index _ =>
        {go (.simulate next (foldedSign negative origin work)) with
          write := (fun t => match t, write with
            | .work (some (half, a)), some symbol =>
                if half = negative ∨ origin = true then oneHot (some symbol) a else keep t
            | _, _ => keep t)
          workDir := fun
            | .input _ => boundedDir (decide (read (.input none) = .one)) inputLetter.isNone input
            | .index _ => boundedDir (decide (read (.index true) = .one))
                (decide (read (.index false) ≠ .one)) index
            | .work _ => foldedDir negative origin work}
  | .halt => go .halt

def tm : NTM (Fintype.card (Tracks M)) where
  Q := State M
  qstart := .boot
  qhalt := .halt
  δ := fun bit q input work output =>
    let a := core M bit q input (fun t => work (trackEquiv M t))
    (a.state, fun i => a.write ((trackEquiv M).symm i), a.output,
      safeDir input a.inputDir,
      fun i => safeDir (work i) (a.workDir ((trackEquiv M).symm i)),
      safeDir output .stay)
  δ_right_of_start := by
    intro bit q input work output
    exact ⟨fun h => by simp [safeDir, h], fun i h => by simp [safeDir, h],
      fun h => by simp [safeDir, h]⟩

/-- Named tracks keep the simulation independent of their numeric enumeration. -/
def config (state : State M) (input : Tape) (work : Tracks M → Tape) (output : Tape) :
    Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  ⟨state, input, fun i => work ((trackEquiv M).symm i), output⟩

theorem step_config (bit : Bool) (q : State M) (input : Tape)
    (work : Tracks M → Tape) (output : Tape) :
    (tm M).stepCfg bit (config M q input work output) =
      let a := core M bit q input.read (fun t => (work t).read)
      config M a.state (input.move (safeDir input.read a.inputDir))
        (fun t => (work t).writeAndMove (a.write t) (safeDir (work t).read (a.workDir t)))
        (output.writeAndMove a.output (safeDir output.read .stay)) := by
  simp [NTM.stepCfg, tm, config]

end
end ComplexityOfGenerators.Simulation.NativeNTM
