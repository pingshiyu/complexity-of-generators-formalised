import ComplexityOfGenerators.Simulation.OutputMatcherSpace
import Complexitylib.Models.TuringMachine.ChoiceTape

/-! Positive tape coordinates, finite alphabet tracks, and the folded native
work tape used by the nondeterministic library translation. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM

open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[simp] theorem toΓ_zero : Γw.zero.toΓ = .zero := rfl
@[simp] theorem toΓ_one : Γw.one.toΓ = .one := rfl
@[simp] theorem toΓ_blank : Γw.blank.toΓ = .blank := rfl
@[simp] theorem toΓ_ne_start (a : Γw) : a.toΓ ≠ .start := by cases a <;> decide

/-- Logical position zero is physical cell one; the marker is never data. -/
def positiveTape (head : ℕ) (cells : ℕ → Γw) : Tape :=
  ⟨head + 1, fun p => if p = 0 then .start else (cells (p - 1)).toΓ⟩

@[simp] theorem positiveTape_read (h : ℕ) (f : ℕ → Γw) :
    (positiveTape h f).read = (f h).toΓ := by simp [positiveTape, Tape.read]

@[simp] theorem positiveTape_start (h : ℕ) (f : ℕ → Γw) :
    (positiveTape h f).StartInvariant := by
  constructor
  · simp [positiveTape]
  · intro p hp
    have hz : p ≠ 0 := by omega
    simp only [positiveTape, hz, ↓reduceIte]
    cases f (p - 1) <;> decide

@[simp] theorem positiveTape_write (h : ℕ) (f : ℕ → Γw) (a : Γw) :
    (positiveTape h f).write a = positiveTape h (Function.update f h a) := by
  apply Tape.ext
  · simp [Tape.write_head, positiveTape]
  funext p
  by_cases zero : p = 0
  · subst p; simp [positiveTape, Tape.write]
  · by_cases same : p = h + 1
    · subst p; simp [positiveTape, Tape.write]
    · have different : p - 1 ≠ h := by omega
      simp [positiveTape, Tape.write, zero, same, different]

@[simp] theorem positiveTape_stay (h : ℕ) (f : ℕ → Γw) :
    (positiveTape h f).move .stay = positiveTape h f := rfl

@[simp] theorem positiveTape_right (h : ℕ) (f : ℕ → Γw) :
    (positiveTape h f).move .right = positiveTape (h + 1) f := rfl

theorem positiveTape_left {h : ℕ} (f : ℕ → Γw) (positive : 0 < h) :
    (positiveTape h f).move .left = positiveTape (h - 1) f := by
  apply Tape.ext
  · simp [positiveTape, Tape.move]; omega
  · rfl

/-- Return the unique marked track; malformed combinations may choose any
marked track, but are never produced by the representation. -/
def decodeTracks {A : Type} (read : A → Γ) : Option A := by
  classical
  exact if h : ∃ a, read a = .one then some h.choose else none

def oneHot {A : Type} [DecidableEq A] (value : Option A) (a : A) : Γw :=
  if value = some a then .one else .blank

@[simp] theorem decodeTracks_oneHot {A : Type} [DecidableEq A] (value : Option A) :
    decodeTracks (fun a => (oneHot value a).toΓ) = value := by
  cases value with
  | none => simp [decodeTracks, oneHot]
  | some a =>
    have present : ∃ b, (oneHot (some a) b).toΓ = .one := ⟨a, by simp [oneHot]⟩
    rw [decodeTracks, dif_pos present]
    have unique (b : A) (hb : (oneHot (some a) b).toΓ = .one) : b = a := by
      by_cases same : a = b
      · exact same.symm
      · simp [oneHot, same, Γw.toΓ] at hb
    exact congrArg some (unique _ present.choose_spec)

/-- Read-only input heads are clamped at both ends, exactly as in the native
model. The end cell is blank even for an empty input. -/
def boundedDir (origin endCell : Bool) : Move → Dir3
  | .stay => .stay
  | .left => if origin then .stay else .left
  | .right => if endCell then .stay else .right

theorem positiveTape_boundedDir (h len : ℕ) (f : ℕ → Γw) (m : Move) (bound : h ≤ len) :
    (positiveTape h f).move (boundedDir (decide (h = 0)) (decide (h = len)) m) =
      positiveTape (m.onInput len h) f := by
  cases m with
  | stay => simp [boundedDir, Move.onInput, Nat.min_eq_left bound]
  | left =>
    by_cases zero : h = 0
    · subst h; simp [boundedDir, Move.onInput]
    · simp only [boundedDir, decide_eq_false zero, Bool.false_eq_true, ↓reduceIte]
      simpa [Move.onInput] using positiveTape_left f (by omega : 0 < h)
  | right =>
    by_cases last : h = len
    · subst h; simp [boundedDir, Move.onInput]
    · have lt : h + 1 ≤ len := by omega
      simp [boundedDir, last, Move.onInput, Nat.min_eq_left lt]

/-- Sign zero is immaterial: either half represents the shared origin. -/
def coordinate (negative : Bool) (p : ℕ) : ℤ := if negative then -(p : ℤ) else p

def foldedDir (negative origin : Bool) (m : Move) : Dir3 :=
  match m with
  | .stay => .stay
  | .left => if origin || negative then .right else .left
  | .right => if origin || !negative then .right else .left

def foldedSign (negative origin : Bool) (m : Move) : Bool :=
  if origin then match m with | .left => true | .right => false | .stay => negative
  else negative

def foldedHead (negative : Bool) (p : ℕ) (m : Move) : ℕ :=
  match foldedDir negative (decide (p = 0)) m with
  | .left => p - 1
  | .right => p + 1
  | .stay => p

@[simp] theorem coordinate_foldedHead (negative : Bool) (p : ℕ) (m : Move) :
    coordinate (foldedSign negative (decide (p = 0)) m) (foldedHead negative p m) =
      m.onInt (coordinate negative p) := by
  cases negative <;> cases m <;> by_cases zero : p = 0
  all_goals simp [foldedHead, foldedDir, foldedSign, coordinate, Move.onInt, zero] <;> omega

theorem positiveTape_foldedDir (negative : Bool) (p : ℕ) (f : ℕ → Γw) (m : Move) :
    (positiveTape p f).move (foldedDir negative (decide (p = 0)) m) =
      positiveTape (foldedHead negative p m) f := by
  cases negative <;> cases m <;> by_cases zero : p = 0
  all_goals simp [foldedHead, foldedDir, zero, Tape.move, positiveTape]
  all_goals congr 1 <;> omega

@[simp] theorem positiveTape_write_current (h : ℕ) (f : ℕ → Γw) :
    (positiveTape h f).write (f h) = positiveTape h f := by
  rw [positiveTape_write, Function.update_eq_self]

@[simp] theorem coordinate_natAbs (negative : Bool) (p : ℕ) :
    (coordinate negative p).natAbs = p := by cases negative <;> simp [coordinate]

theorem coordinate_eq_iff (a b : Bool) (i j : ℕ) :
    coordinate a i = coordinate b j ↔ i = j ∧ (a = b ∨ j = 0) := by
  cases a <;> cases b <;> simp [coordinate] <;> omega

/-- At the shared origin both half-tapes are written; elsewhere only the
active half changes. -/
theorem folded_write {A : Type} [DecidableEq A] (w : ℤ → Option A)
    (negative half : Bool) (p : ℕ) (a symbol : A) :
    (positiveTape p (fun r => oneHot (w (coordinate half r)) a)).write
        (if half = negative ∨ p = 0 then oneHot (some symbol) a
         else oneHot (w (coordinate half p)) a : Γw) =
      positiveTape p (fun r => oneHot
        (Function.update w (coordinate negative p) (some symbol) (coordinate half r)) a) := by
  rw [positiveTape_write]
  congr 1
  funext r
  by_cases same : r = p
  · subst r
    simp only [Function.update_self]
    by_cases active : half = negative ∨ p = 0
    · rw [if_pos active, (coordinate_eq_iff half negative p p).mpr ⟨rfl, active⟩, Function.update_self]
    · rw [if_neg active, Function.update_of_ne (by simpa [coordinate_eq_iff] using active)]
  · rw [Function.update_of_ne same, Function.update_of_ne (by simp [coordinate_eq_iff, same])]

end
end ComplexityOfGenerators.Simulation.NativeNTM
