import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind
import Complexitylib.Models.TuringMachine

/-! The library's protected origin is implicit in the bank representation.
All other nonnegative cells store their actual symbol, including writable blank.
Negative positions are unused. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM

open TransducerBank
set_option backward.isDefEq.respectTransparency false

def image (t : Complexity.Tape) (i : ℤ) : Complexity.Γ :=
  if 0 < i then t.cells i.toNat else .blank

def read (origin : Bool) (cell : Complexity.Γ) : Complexity.Γ :=
  if origin then .start else cell

def move (origin : Bool) : Complexity.Dir3 → Move
  | .left => if origin then .stay else .left
  | .right => .right
  | .stay => .stay

def write (origin : Bool) (symbol : Complexity.Γ) : Complexity.Γ :=
  if origin then .blank else symbol

theorem read_image (t : Complexity.Tape) (marker : t.cells 0 = .start) :
    read (decide ((t.head : ℤ) = 0)) (image t t.head) = t.read := by
  by_cases zero : t.head = 0
  · simp [read, zero, Complexity.Tape.read, marker]
  · simp [read, image, zero, Complexity.Tape.read, Nat.pos_of_ne_zero zero]

theorem move_head (t : Complexity.Tape) (direction : Complexity.Dir3) :
    (move (decide ((t.head : ℤ) = 0)) direction).onInt t.head =
      ((t.move direction).head : ℤ) := by
  cases direction <;> by_cases zero : t.head = 0 <;>
    simp [move, Move.onInt, Complexity.Tape.move, zero]
  all_goals omega

theorem write_image (t : Complexity.Tape) (symbol : Complexity.Γ) :
    Function.update (image t) (t.head : ℤ)
      (write (decide ((t.head : ℤ) = 0)) symbol) = image (t.write symbol) := by
  funext i
  by_cases zero : t.head = 0
  · by_cases atHead : i = 0
    · subst i; simp [write, image, zero]
    · simp [write, Complexity.Tape.write, zero, atHead]
  · by_cases atHead : i = (t.head : ℤ)
    · subst i
      simp [write, image, Complexity.Tape.write, zero, Nat.pos_of_ne_zero zero]
    · have different : 0 < i → i.toNat ≠ t.head := by omega
      simp only [Function.update_of_ne atHead, Complexity.Tape.write, zero, ↓reduceIte]
      simp only [image]
      split_ifs with positive
      · exact (Function.update_of_ne (different positive) _ _).symm
      · rfl

theorem writeAndMove_head (t : Complexity.Tape) (symbol : Complexity.Γ)
    (direction : Complexity.Dir3) :
    (t.writeAndMove symbol direction).head = (t.move direction).head := by
  cases direction <;> simp [Complexity.Tape.writeAndMove, Complexity.Tape.move,
    Complexity.Tape.write_head]

theorem image_move (t : Complexity.Tape) (direction : Complexity.Dir3) :
    image (t.move direction) = image t := by cases direction <;> rfl

theorem write_read (t : Complexity.Tape) : t.write t.read = t := by
  simp [Complexity.Tape.write, Complexity.Tape.read, Function.update_eq_self]

end ComplexityOfGenerators.Simulation.LibraryTM
