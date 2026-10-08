import ComplexityOfGenerators.Simulation.RoutineComposition
import ComplexityOfGenerators.Simulation.PostMachine
import ComplexityOfGenerators.Simulation.PrimitiveOperations
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-!
# A finite-control routine for a virtual unary index

The physical work tape has five tracks: the source work symbol, the origin,
the unary index, the virtual index head, and the source work head. The routine
scans to the index head to select a source instruction, updates the index head,
and returns to the source work head to execute the work/output part.

The transition table inspects one finite symbol at a time. In particular, the
virtual index length and head positions do not occur in finite control. This
module defines the routine and its tape representation; its execution proofs
are separate from the loading and routine-composition proofs.
-/

namespace ComplexityOfGenerators.Simulation

structure IndexCell (symbols : ℕ) where
  source : Option (Fin symbols)
  origin : Bool
  live : Bool
  indexHead : Bool
  workHead : Bool
  deriving DecidableEq, Fintype

instance {symbols : ℕ} : Inhabited (IndexCell symbols) :=
  ⟨⟨none, false, false, false, false⟩⟩

noncomputable section

local instance : Fintype Move := Fintype.ofFinite _

structure IndexAction (O : Type) (states symbols : ℕ) where
  next : Fin states
  write : Option (Fin symbols)
  move : Move
  emit : Option O
  deriving Fintype

inductive IndexPhase (O : Type) (states symbols : ℕ)
  | source (q : Fin states) (negative : Bool)
  | toOrigin (q : Fin states) (negative : Bool) (cached : Option (Fin symbols))
  | toIndex (q : Fin states) (negative : Bool) (cached : Option (Fin symbols))
  | placeIndex (action : IndexAction O states symbols) (negative : Bool)
  | returnOrigin (action : IndexAction O states symbols) (negative : Bool)
  | returnWork (action : IndexAction O states symbols) (negative : Bool)
  | execute (action : IndexAction O states symbols) (negative : Bool)
  | placeWork (q : Fin states) (negative : Bool)
  deriving Fintype

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

def indexAlphabet : IndexCell M.symbols ≃ Fin (Fintype.card (IndexCell M.symbols)) :=
  Fintype.equivFin _

def indexControl : IndexPhase O M.states M.symbols ≃
    Fin (Fintype.card (IndexPhase O M.states M.symbols)) := Fintype.equivFin _

def indexRead (work : Option (Fin (Fintype.card (IndexCell M.symbols) + 1))) : IndexCell M.symbols :=
  bootDecode (indexAlphabet M) work

def indexWrite (cell : IndexCell M.symbols) : Fin (Fintype.card (IndexCell M.symbols) + 1) :=
  bootEncode (indexAlphabet M) cell

omit [Fintype O] in
@[simp] theorem indexRead_write (cell : IndexCell M.symbols) :
    indexRead M (some (indexWrite M cell)) = cell := bootDecode_encode _ _

/-- The explicit origin and unary-end tracks implement both clamped boundaries. -/
def virtualIndexMove (cell : IndexCell M.symbols) : Move → Move
  | .left => if cell.origin then .stay else .left
  | .stay => .stay
  | .right => if cell.live then .right else .stay

def workSideAfter (cell : IndexCell M.symbols) (negative : Bool) (move : Move) : Bool :=
  if cell.origin then decide (move = .left) else negative

def indexResume (q : Fin M.states) : IndexAction O M.states M.symbols :=
  ⟨q, none, .stay, none⟩

def virtualIndexTransition (phase : IndexPhase O M.states M.symbols)
    (raw : Option (Fin (Fintype.card (IndexCell M.symbols) + 1))) :
    Instruction O (Fintype.card (IndexPhase O M.states M.symbols))
      (Fintype.card (IndexCell M.symbols) + 1) :=
  let cell := indexRead M raw
  let silent := fun phase move => Instruction.step (indexControl M phase) none move .stay .stay .stay none
  match phase with
  | .source q negative => silent (.toOrigin q negative cell.source) .stay
  | .toOrigin q negative cached =>
      if cell.origin then silent (.toIndex q negative cached) .stay
      else silent phase (if negative then .right else .left)
  | .toIndex q negative cached =>
      if !cell.indexHead then silent phase .right
      else match M.transition q none none (if cell.live then some true else none) cached with
        | .accept => .accept
        | .reject => .reject
        | .readRandom no yes => .readRandom
            (indexControl M (.returnOrigin (indexResume M no) negative))
            (indexControl M (.returnOrigin (indexResume M yes) negative))
        | .step next write work _ _ index emit =>
            .step (indexControl M (.placeIndex ⟨next, write, work, emit⟩ negative))
              (some (indexWrite M {cell with indexHead := false}))
              (virtualIndexMove M cell index) .stay .stay .stay none
  | .placeIndex action negative =>
      .step (indexControl M (.returnOrigin action negative))
        (some (indexWrite M {cell with indexHead := true})) .stay .stay .stay .stay none
  | .returnOrigin action negative =>
      if cell.origin then silent (.returnWork action negative) .stay else silent phase .left
  | .returnWork action negative =>
      if cell.workHead then silent (.execute action negative) .stay
      else silent phase (if negative then .left else .right)
  | .execute action negative =>
      .step (indexControl M (.placeWork action.next (workSideAfter M cell negative action.move)))
        (some (indexWrite M {cell with
          source := match action.write with | none => cell.source | some symbol => some symbol
          workHead := false})) action.move .stay .stay .stay action.emit
  | .placeWork q negative =>
      .step (indexControl M (.source q negative))
        (some (indexWrite M {cell with workHead := true})) .stay .stay .stay .stay none

/-- A routine over the same work alphabet as the block loader. Its initial tape
must be prepared by the loader; this is not a machine with a magically supplied
initial work tape. -/
def virtualIndexRoutine : Routine Unit Bool O (Fintype.card (IndexCell M.symbols) + 1) where
  states := Fintype.card (IndexPhase O M.states M.symbols)
  initial := indexControl M (.source M.initial false)
  transition := fun state _ _ _ raw => virtualIndexTransition M ((indexControl M).symm state) raw

def virtualIndexCell (length : ℕ) (work : ℤ → Option (Fin M.symbols))
    (indexHead workHead : Option ℤ) (i : ℤ) : IndexCell M.symbols where
  source := work i
  origin := decide (i = 0)
  live := decide (0 ≤ i ∧ i < (length : ℤ))
  indexHead := decide (indexHead = some i)
  workHead := decide (workHead = some i)

/-- Optional markers allow the invariant to describe the intermediate step
between clearing a head marker and writing it at its new position. -/
def VirtualIndexMemory (length : ℕ) (work : ℤ → Option (Fin M.symbols))
    (indexHead workHead : Option ℤ)
    (memory : ℤ → Option (Fin (Fintype.card (IndexCell M.symbols) + 1))) : Prop :=
  ∀ i, indexRead M (memory i) = virtualIndexCell M length work indexHead workHead i

omit [Fintype O] in
theorem virtualIndexMove_correct (length head : ℕ) (bound : head ≤ length)
    (work : ℤ → Option (Fin M.symbols)) (ih wh : Option ℤ) (move : Move) :
    (virtualIndexMove M (virtualIndexCell M length work ih wh head) move).onInt (head : ℤ) =
      ((move.onInput length head : ℕ) : ℤ) := by
  cases move with
  | left =>
      by_cases zero : head = 0
      · simp [virtualIndexMove, virtualIndexCell, Move.onInt, Move.onInput, zero]
      · simp [virtualIndexMove, virtualIndexCell, Move.onInt, Move.onInput, zero]
        omega
  | stay => simp [virtualIndexMove, Move.onInt, Move.onInput, Nat.min_eq_left bound]
  | right =>
      by_cases live : head < length <;>
        simp [virtualIndexMove, virtualIndexCell, Move.onInt, Move.onInput, live] <;> omega

omit [Fintype O] in
/-- The finite side bit remains valid when the source work head crosses zero.
Either value is allowed at zero, where the origin track determines the next move. -/
theorem workSideAfter_correct (length : ℕ) (work : ℤ → Option (Fin M.symbols))
    (ih wh : Option ℤ) (head : ℤ) (negative : Bool) (move : Move)
    (side : if negative then head ≤ 0 else 0 ≤ head) :
    if workSideAfter M (virtualIndexCell M length work ih wh head) negative move then
      move.onInt head ≤ 0 else 0 ≤ move.onInt head := by
  cases negative <;> cases move <;>
    simp_all [workSideAfter, virtualIndexCell, Move.onInt] <;> omega

end

end ComplexityOfGenerators.Simulation
