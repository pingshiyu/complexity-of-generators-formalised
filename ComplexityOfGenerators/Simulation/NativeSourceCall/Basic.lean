import ComplexityOfGenerators.Simulation.WorkSteps
import ComplexityOfGenerators.Simulation.PrimitiveOperations
import ComplexityOfGenerators.Simulation.RoutineComposition
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-! A native source-call routine with a moving, bounded virtual-index packet.

The source work tape keeps its ordinary absolute coordinates. Only its unary
index and index-head marker move alongside the source work head. The `fixed`
track is reserved for the suspended outer controller and is never modified.
Outputs and random reads are passed through directly: no source output, work
snapshot, or elapsed-time counter is copied into the bounded controller.

This is a subroutine, not a standalone generator: its packet and origin/visit
tracks must be prepared by actual caller instructions. Acceptance clears the
packet and the source's visited work interval and returns to the origin.
Execution and quantitative correctness are proved in the companion modules. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall

@[ext] structure IndexMark where
  first : Bool
  last : Bool
  head : Bool
  deriving DecidableEq, Fintype

@[ext] structure Cell (F : Type) (symbols : ℕ) where
  fixed : F
  source : Option (Fin symbols)
  origin : Bool
  visited : Bool
  packet : Option IndexMark
  deriving Fintype

instance {F : Type} [Inhabited F] {symbols : ℕ} : Inhabited (Cell F symbols) :=
  ⟨⟨default, none, false, false, none⟩⟩

noncomputable section
local instance : Fintype Move := Fintype.ofFinite _
set_option synthInstance.maxSize 4096

structure Action (O : Type) (states symbols : ℕ) where
  next : Fin states
  write : Option (Fin symbols)
  move : Move
  emit : Option O
  deriving Fintype

inductive Return (O : Type) (states symbols : ℕ)
  | resume (q : Fin states)
  | step (action : Action O states symbols)
  | accepted
  deriving Fintype

inductive Phase (O : Type) (states symbols : ℕ)
  | source (q : Fin states)
  | fetch (q : Fin states) (cached : Option (Fin symbols))
  | placeIndex (action : Action O states symbols)
  | returning (action : Return O states symbols)
  | execute (action : Action O states symbols)
  | rightBegin (q : Fin states)
  | rightCarry (q : Fin states) (carry : IndexMark)
  | rightReturn (q : Fin states)
  | leftEnd (q : Fin states)
  | leftCarry (q : Fin states) (carry : IndexMark)
  | arrive (q : Fin states)
  | clearEnd
  | clearPacket
  | cleanupLeft
  | cleanupRight
  | cleanupOrigin
  | done
  deriving Fintype

variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O)

def alphabet : Cell F M.symbols ≃ Fin (Fintype.card (Cell F M.symbols)) := Fintype.equivFin _
def control : Phase O M.states M.symbols ≃ Fin (Fintype.card (Phase O M.states M.symbols)) :=
  Fintype.equivFin _

def read (raw : Option (Fin (Fintype.card (Cell F M.symbols)))) : Cell F M.symbols :=
  raw.elim default (alphabet M).symm

@[simp] theorem read_write (cell : Cell F M.symbols) :
    read M (some (alphabet M cell)) = cell := by simp [read]

/-- Both endpoints are represented in the packet, including when its length is
zero. The virtual index contains `j` live cells and one right blank cell. -/
def indexMove (mark : IndexMark) : Move → Move
  | .left => if mark.first then .stay else .left
  | .stay => .stay
  | .right => if mark.last then .stay else .right

def transition (phase : Phase O M.states M.symbols)
    (raw : Option (Fin (Fintype.card (Cell F M.symbols)))) :
    Instruction O (Fintype.card (Phase O M.states M.symbols)) (Fintype.card (Cell F M.symbols)) :=
  let cell := read M raw
  let silent := fun phase move => Instruction.step (control M phase) none move .stay .stay .stay none
  let update := fun phase cell move emit => Instruction.step (control M phase)
    (some (alphabet M cell)) move .stay .stay .stay emit
  match phase with
  | .source q => silent (.fetch q cell.source) .stay
  | .fetch q cached =>
      match cell.packet with
      | none => .reject
      | some mark =>
          if !mark.head then silent phase .right
          else match M.transition q none none (if mark.last then none else some ()) cached with
          | .accept => silent (.returning .accepted) .stay
          | .reject => .reject
          | .readRandom no yes => .readRandom
              (control M (.returning (.resume no))) (control M (.returning (.resume yes)))
          | .step next write move _ _ index emit =>
              update (.placeIndex ⟨next, write, move, emit⟩)
                {cell with packet := some {mark with head := false}} (indexMove mark index) none
  | .placeIndex action =>
      match cell.packet with
      | none => .reject
      | some mark => update (.returning (.step action))
          {cell with packet := some {mark with head := true}} .stay none
  | .returning action =>
      if cell.packet.any IndexMark.first then
        match action with
        | .resume q => silent (.source q) .stay
        | .step action => silent (.execute action) .stay
        | .accepted => silent .clearEnd .stay
      else silent phase .left
  | .execute action =>
      let next := match action.move with
        | .stay => Phase.source action.next
        | .right => .rightBegin action.next
        | .left => .leftEnd action.next
      update next {cell with source := action.write.or cell.source} .stay action.emit
  | .rightBegin q =>
      match cell.packet with
      | none => .reject
      | some mark => update (.rightCarry q mark) {cell with packet := none} .right none
  | .rightCarry q carry =>
      if carry.last then update (.rightReturn q) {cell with packet := some carry} .stay none
      else match cell.packet with
        | none => .reject
        | some old => update (.rightCarry q old) {cell with packet := some carry} .right none
  | .rightReturn q =>
      if cell.packet.any IndexMark.first then silent (.arrive q) .stay else silent phase .left
  | .leftEnd q =>
      match cell.packet with
      | none => .reject
      | some mark => if mark.last then
          update (.leftCarry q mark) {cell with packet := none} .left none
        else silent phase .right
  | .leftCarry q carry =>
      if carry.first then update (.arrive q) {cell with packet := some carry} .stay none
      else match cell.packet with
        | none => .reject
        | some old => update (.leftCarry q old) {cell with packet := some carry} .left none
  | .arrive q => update (.source q) {cell with visited := true} .stay none
  | .clearEnd =>
      if cell.packet.any IndexMark.last then silent .clearPacket .stay else silent phase .right
  | .clearPacket =>
      let next := if cell.packet.any IndexMark.first then Phase.cleanupLeft else .clearPacket
      update next {cell with packet := none}
        (if cell.packet.any IndexMark.first then .stay else .left) none
  | .cleanupLeft =>
      if cell.visited then silent phase .left else silent .cleanupRight .right
  | .cleanupRight =>
      if cell.visited then update phase {cell with source := none, visited := false} .right none
      else silent .cleanupOrigin .left
  | .cleanupOrigin =>
      if cell.origin then silent .done .stay else silent phase .left
  | .done => .accept

def routine : Routine Unit Bool O (Fintype.card (Cell F M.symbols)) where
  states := Fintype.card (Phase O M.states M.symbols)
  initial := control M (.source M.initial)
  transition := fun state _ _ _ raw => transition M ((control M).symm state) raw

def machine : Machine Unit Bool O := (routine (F := F) M).machine

@[simp] theorem machine_transition (phase : Phase O M.states M.symbols)
    (input auxiliary index raw) :
    (machine (F := F) M).transition (control M phase) input auxiliary index raw = transition M phase raw := by
  simp [machine, routine, Routine.machine]

/-- Every write preserves the fixed outer-controller track. -/
theorem transition_fixed (phase : Phase O M.states M.symbols) (raw)
    (next write work input auxiliary index emit)
    (action : transition (F := F) M phase raw = .step next write work input auxiliary index emit) :
    ∀ symbol ∈ write, (read M (some symbol)).fixed = (read M raw).fixed := by
  cases phase <;> simp only [transition] at action <;>
    repeat' first | split at action | cases h : (read M raw).packet <;> simp only [h] at action
  all_goals
    first
    | cases action; simp
    | contradiction

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
