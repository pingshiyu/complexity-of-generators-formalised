import ComplexityOfGenerators.Proofs.LibrarySpace

/-! Executable regressions for the actual compiler's bank transition table.
The general native simulation and visited-space bounds are proved in LibraryTM.
Run with `lake env lean scripts/CheckLibraryTM.lean` after `lake build`. -/

open ComplexityOfGenerators ComplexityOfGenerators.Simulation

namespace LibraryTMChecks

def direction (symbol : Complexity.Γ) (desired : Complexity.Dir3) : Complexity.Dir3 :=
  if symbol = .start then .right else desired

/-- Read the first input bit into a work cell, then copy it to the output while
erasing the work cell. Move the output head away and back before halting. -/
def exampleMachine : Complexity.TM 1 where
  Q := Fin 5
  qstart := 0
  qhalt := 4
  δ := fun q input work output =>
    (if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 3 else 4,
      fun _ => if q = 1 ∧ input = .one then .one else .blank,
      if q = 2 ∧ work 0 = .one then .one else if q = 3 then .blank else .zero,
      direction input .right,
      fun i => direction (work i) (if q = 2 then .left else .stay),
      direction output (if q = 2 then .right else if q = 3 then .left else .stay))
  δ_right_of_start := by
    intro q input work output
    exact ⟨fun h => by simp [direction, h], fun i h => by simp [direction, h],
      fun h => by simp [direction, h]⟩

/-- Zero work tapes and an initially halted source exercise the smallest bank. -/
def initiallyHalted : Complexity.TM 0 where
  Q := Unit
  qstart := ()
  qhalt := ()
  δ := fun _ _ _ _ => ((), fun _ => .blank, .blank, .right, fun _ => .right, .right)
  δ_right_of_start := by intros; exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- Swap two distinct work symbols simultaneously, then verify the swap before
erasing both. Reading a tape after committing the other write would fail. -/
def swapMachine : Complexity.TM 2 where
  Q := Fin 5
  qstart := 0
  qhalt := 4
  δ := fun q input work output =>
    (if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 3 else 4,
      fun i => if q = 1 then (if i = 0 then .one else .zero)
        else if q = 2 then (if work (if i = 0 then 1 else 0) = .one then .one else .zero)
        else .blank,
      if q = 3 ∧ work 0 = .zero ∧ work 1 = .one then .one else .zero,
      direction input .stay, fun i => direction (work i) .stay, direction output .stay)
  δ_right_of_start := by
    intro q input work output
    exact ⟨fun h => by simp [direction, h], fun i h => by simp [direction, h],
      fun h => by simp [direction, h]⟩

def sourceResult {k : ℕ} (M : Complexity.TM k) (word : BitString) (fuel : ℕ) : Option Bool :=
  let rec loop : ℕ → Complexity.Cfg k M.Q → Option Bool
    | 0, _ => none
    | f + 1, c => match M.step c with
      | none => some (c.output.cells 1 == .one)
      | some d => loop f d
  loop fuel (M.initCfg word)

def bankResult {k : ℕ} (M : Complexity.TM k) (word : BitString) (fuel : ℕ) : Option Bool :=
  let B := LibraryTM.bank M
  let data := decisionData word
  let rec loop : ℕ → LibraryTM.Config M → Option Bool
    | 0, _ => none
    | f + 1, c => match B.instruction data c with
      | .accept => some true
      | .reject => some false
      | .readRandom _ _ => none
      | .step q symbol work input auxiliary index emit =>
          loop f (B.advance data c q symbol work input auxiliary index emit)
  loop fuel B.initialConfiguration

#guard sourceResult exampleMachine [true, false] 10 == some true
#guard sourceResult exampleMachine [false, true] 10 == some false
#guard sourceResult exampleMachine [] 10 == some false
#guard bankResult exampleMachine [true, false] 100 == some true
#guard bankResult exampleMachine [false, true] 100 == some false
#guard bankResult exampleMachine [] 100 == some false
#guard bankResult exampleMachine [true] 100 == sourceResult exampleMachine [true] 10
#guard bankResult initiallyHalted [] 20 == some false
#guard bankResult initiallyHalted [true, false, true] 30 == some false
#guard sourceResult swapMachine [] 10 == some true
#guard bankResult swapMachine [] 100 == some true

end LibraryTMChecks
