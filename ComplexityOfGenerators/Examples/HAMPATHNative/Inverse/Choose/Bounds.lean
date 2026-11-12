import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Fields
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Force
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.PrefixBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.PositionBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelBitsBounds
import ComplexityOfGenerators.Simulation.WordStack.RoutineResources

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose
open Simulation.WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] candidate incidents positionPrepare position LabelBits.routine

theorem candidate_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) (range : 2^(s 38).length ≤ budget) :
    StoreBound (candidate.eval s) (10*(budget+1)) ∧ candidate.cost s ≤ 3000*(budget+1)^2 := by
  let taken := (TakeWord.routine (S := Symbol) (O := Symbol) candidateSlots).eval s
  let copied := (Routine.assign (O := Symbol) 38 19 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval taken
  let decoded := ((LabelBits.routine (O := Symbol)).rename Output.low32).eval copied
  have takenSize : StoreBound taken budget := TakeWord.routine_bound candidateSlots s budget sizes
  have takenCost := TakeWord.routine_cost (O := Symbol) candidateSlots s budget sizes
  have copiedSize : StoreBound copied budget := takenSize.assign _ _ _ _ _ _ _
  have copiedCost := Classify.assign_cost 38 19 48 (by decide) (by decide) (by decide) (fun _ => .bit true) taken budget takenSize
  have lowSize : StoreBound (copied ∘ Output.low32) budget := fun j => copiedSize _
  have width : ((copied ∘ Output.low32) 19).length = (s 38).length := by
    change (copied 19).length = (s 38).length
    simp [copied,Routine.assign_eval,taken,TakeWord.routine_eval,candidateSlots]
  have native := LabelBits.routine_bound (O := Symbol) (copied ∘ Output.low32) budget lowSize (by rw [width]; exact range)
  have decodedSize : StoreBound decoded (10*(budget+1)) := Classify.call32_bound _ copied budget _ copiedSize (by omega) native.1
  have decodedCost : ((LabelBits.routine (O := Symbol)).rename Output.low32).cost copied ≤ 2000*(budget+1)^2 := by
    simpa only [Routine.rename_cost] using native.2
  have finalCost := Classify.assign_cost 28 40 48 (by decide) (by decide) (by decide) (fun _ => .bit true) decoded (10*(budget+1)) decodedSize
  constructor
  · unfold candidate
    exact decodedSize.assign 28 40 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)
  · unfold candidate
    change (TakeWord.routine (O := Symbol) candidateSlots).cost s+1+
      ((Routine.assign (O := Symbol) 38 19 48 _ _ _ (fun _ => .bit true)).cost taken+1+
        (((LabelBits.routine (O := Symbol)).rename Output.low32).cost copied+1+
          (Routine.assign (O := Symbol) 28 40 48 _ _ _ (fun _ => .bit true)).cost decoded)) ≤ _
    nlinarith

theorem incidents_resources (budget : ℕ) :
    Routine.ResourceBound incidents budget budget (210*(budget+1)) := by
  have result := (Routine.ResourceBound.takeWord (S := Symbol) (O := Symbol) incomingSlots budget).seq
    (Routine.ResourceBound.takeWord outgoingSlots budget)
  unfold incidents
  exact result.weaken le_rfl le_rfl (by omega)

theorem positionPrepare_resources (budget : ℕ) :
    Routine.ResourceBound positionPrepare budget budget (100*(budget+1)) := by
  have result := (Routine.ResourceBound.assign (S := Symbol) (O := Symbol) (k := 64) 35 0 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) budget).seq
    ((Routine.ResourceBound.assign (S := Symbol) (O := Symbol) (k := 64) 36 1 48 (by decide) (by decide) (by decide) (fun _ => .bit true) budget).seq
      ((Routine.ResourceBound.assign (S := Symbol) (O := Symbol) (k := 64) 39 2 48 (by decide) (by decide) (by decide) (fun _ => .bit true) budget).seq
        (Routine.ResourceBound.assign (S := Symbol) (O := Symbol) (k := 64) 40 3 48 (by decide) (by decide) (by decide) (fun _ => .bit true) budget)))
  unfold positionPrepare
  exact result.weaken le_rfl le_rfl (by omega)

theorem position_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (position.eval s) (budget+3) ∧ position.cost s ≤ 3000*(budget+4) := by
  let prepared := positionPrepare.eval s
  let selected := ((Position.routine (O := Symbol)).rename low12).eval prepared
  let copied := (Routine.assign (O := Symbol) 4 40 48 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval selected
  have preparedResult := positionPrepare_resources budget s sizes
  have native : Routine.ResourceBound (Position.routine (O := Symbol)) budget (budget+3) (2000*(budget+3)) := by
    intro source bounded
    exact Position.routine_bound source budget bounded
  have selectedResult := native.rename low12 (by omega) prepared preparedResult.1
  have copiedSize : StoreBound copied (budget+3) := selectedResult.1.assign _ _ _ _ _ _ _
  have copiedCost := Classify.assign_cost 4 40 48 (by decide) (by decide) (by decide) (fun _ => .bit true) selected (budget+3) selectedResult.1
  have checked := Classify.require_bound 5 true copied (budget+3) copiedSize
  constructor
  · unfold position
    exact checked.1
  · have prepareCost := preparedResult.2
    have selectedCost := selectedResult.2
    have checkedCost := checked.2
    unfold position
    change positionPrepare.cost s+1+(((Position.routine (O := Symbol)).rename low12).cost prepared+1+
      ((Routine.assign (O := Symbol) 4 40 48 _ _ _ (fun _ => .bit true)).cost selected+1+(Classify.require 5 true).cost copied)) ≤ _
    omega

theorem forceEdge_resources (budget : ℕ) :
    Routine.ResourceBound forceEdge budget (budget+1) (130*(budget+2)) := by
  have result := (Routine.ResourceBound.dropAt (S := Symbol) (O := Symbol) forceSlots (Symbol.bit true) budget).seq
    (Routine.ResourceBound.insertAt (S := Symbol) (O := Symbol) forceSlots (Symbol.bit true) (Symbol.bit true) budget)
  unfold forceEdge
  exact result.weaken le_rfl le_rfl (by omega)

def storeBudget (input : ℕ) : ℕ := 10*(input+1)+4
def stackBudget (input : ℕ) : ℕ := 100000*(input+4)^2

/-- Every native inverse choice is bounded for arbitrary source words and
scratch contents. Only the binary label width needs its natural unary range
bound, supplied by the classifier's logarithm metadata. -/
theorem routine_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) (range : 2^(s 38).length ≤ budget) :
    StoreBound (routine.eval s) (storeBudget budget) ∧ routine.cost s ≤ stackBudget budget := by
  change StoreBound (routine.eval s) (10*(budget+1)+4) ∧ routine.cost s ≤ 100000*(budget+4)^2
  let a := candidate.eval s
  let b := incidents.eval a
  let c := position.eval b
  have first := candidate_bound s budget sizes range
  have second := incidents_resources (10*(budget+1)) a first.1
  have third := position_bound b (10*(budget+1)) second.1
  have fourth := forceEdge_resources (10*(budget+1)+3) c third.1
  constructor
  · rw [routine_eval]
    exact fourth.1
  · have aCost := first.2
    have bCost := second.2
    have cCost := third.2
    have dCost := fourth.2
    unfold routine
    change candidate.cost s+1+(incidents.cost a+1+(position.cost b+1+forceEdge.cost c)) ≤ _
    nlinarith

theorem sampleClock_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (sampleClock.eval s) (3*budget) ∧ sampleClock.cost s ≤ 60*(budget+1) := by
  constructor
  · rw [sampleClock_eval]
    apply (sizes.mono (by omega)).clear 48 |>.update 46
    simp only [List.length_replicate]
    have width := sizes 38
    have child := sizes 35
    omega
  · have width := sizes 38
    have child := sizes 35
    have old := sizes 46
    have scratch := sizes 48
    simp [sampleClock,Routine.seq,Routine.assign_cost,Routine.assign_eval,Routine.copy]
    omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose
