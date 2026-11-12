import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Sampling
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Output.Bounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency true

theorem prepared_bound (n : ℕ) (target label : List Symbol)
    (targetBound : target.length≤n) (labelBound : label.length≤n) :
    StoreBound (preparedStore n target label) (n+1) := by
  unfold preparedStore
  apply StoreBound.update
  · apply StoreBound.update
    · apply StoreBound.update
      · intro j
        simp
      · exact targetBound.trans (by omega)
    · exact labelBound.trans (by omega)
  · simp

theorem input_cost (n : ℕ) (target label : List Symbol) :
    input.cost (indexed n target label).store=6*target.length+6*label.length+4 := by
  simp [input,Routine.seq,Routine.clearMany,Routine.skip,Routine.ofLocal,Local.ticks,
    Routine.clear,Routine.transfer,indexed,Command.loadedIndex,Memory.set,loaded]
  omega

theorem sampleClock_cost (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    Choose.sampleClock.cost s≤60*(budget+1) := by
  have source := sizes 35
  have width := sizes 38
  have output := sizes 46
  have scratch := sizes 48
  simp [Choose.sampleClock,Routine.seq,Routine.assign_cost,Routine.copy,Routine.assign_eval]
  omega

theorem counted_bound (m : Memory) (budget : ℕ) (sizes : StoreBound m.store budget)
    (room : (m.store 38).length+2*(m.store 35).length≤budget) : StoreBound (counted m).store budget := by
  change StoreBound (Choose.sampleClock.eval m.store) budget
  rw [Choose.sampleClock_eval]
  exact (sizes.clear 48).update 46 _ (by simpa using room)

theorem sampled_bound (bits : BitString) (m : Memory) (budget : ℕ) (sizes : StoreBound m.store budget)
    (room : (m.store 38).length+2*(m.store 35).length≤budget) : StoreBound (sampled bits m).store budget := by
  have source := counted_bound m budget sizes room
  change StoreBound (Function.update (Function.update (Function.update (counted m).store 46 []) 47 []) 42
    (((bits.drop (counted m).randomHead).take ((counted m).store 46).length).map Symbol.bit)) budget
  apply ((source.clear 46).clear 47).update 42
  simp only [List.length_map,List.length_take]
  exact (Nat.min_le_left _ _).trans (source 46)

theorem sampled_width (bits : BitString) (m : Memory) : (sampled bits m).store 38=m.store 38 := by
  simp [sampled,Command.forwardCollected,counted,Choose.sampleClock_eval]

theorem finishBudget_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    finishBudget s≤Output.stackBudget budget+4*Output.storeBudget budget+2 := by
  have output := Output.routine_bound s budget sizes
  have length := output.1 31
  unfold finishBudget
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
