import ComplexityOfGenerators.Simulation.StarPaths.Validation

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] validationFactor validationBody validationLoop validationSetup validationRoutine

private theorem validationBody_empty {O : Type} (s : Store) (empty : s 16 = []) :
    (validationBody (O := O)).eval s = s := by
  simp [validationBody,WordStack.Routine.branch,empty,WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.eval]

private theorem validationBody_cons {O : Type} (flags : List Bool) (j : ℕ) (rest : Parts) (s : Store)
    (positive : 0 < j) (input : s 16 = payload (j::rest)) (source : s 25 = flagsWord flags) :
    (validationBody (O := O)).eval s 16 = payload rest ∧
      (validationBody (O := O)).eval s 20 = if (flags[j-1]?).getD false then s 20 else [] := by
  have present : (s 16).head?.isSome = true := by rw [input]; rfl
  simpa only [validationBody,WordStack.Routine.branch,present,ite_true] using
    validationFactor_result (O := O) flags j rest s positive input source

/-- At most n positive factors occur. The native validation loop therefore
finishes every proposed factor and checks exactly the certified source flags. -/
theorem counted_validation {O : Type} (flags : List Bool) (parts : Parts) (count : ℕ) (s : Store)
    (positive : ∀ j ∈ parts, 0 < j) (enough : parts.length ≤ count)
    (input : s 16 = payload parts) (source : s 25 = flagsWord flags) :
    let output := ((WordStack.Routine.counted 18 (validationBody (O := O))).eval^[count] s)
    output 16 = [] ∧ output 20 = if allowed flags parts then s 20 else [] := by
  induction count generalizing parts s with
  | zero =>
      have empty : parts = [] := List.length_eq_zero_iff.mp (by omega)
      subst parts
      simpa [payload,allowed] using And.intro input (Eq.refl (s 20))
  | succ count ih =>
      let popped := Function.update s 18 (s 18).tail
      let ready := (WordStack.Routine.counted 18 (validationBody (O := O))).eval s
      have step : ready = (validationBody (O := O)).eval popped := rfl
      have readySource : ready 25 = flagsWord flags := by
        rw [step,validationBody_frame 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simpa [popped] using source
      rw [Function.iterate_succ_apply]
      cases parts with
      | nil =>
          have readyEq : ready = popped := by
            rw [step]
            apply validationBody_empty
            simpa [popped,payload] using input
          have readyInput : ready 16 = payload [] := by rw [readyEq]; simpa [popped,payload] using input
          have result := ih [] ready (by simp) (by simp) readyInput readySource
          have same : ready 20 = s 20 := by rw [readyEq]; simp [popped]
          simpa only [allowed,List.all_nil,ite_true,same] using result
      | cons j rest =>
          have firstPositive := positive j (by simp)
          have tailPositive : ∀ k ∈ rest, 0 < k := fun k member => positive k (by simp [member])
          have first := validationBody_cons (O := O) flags j rest popped firstPositive
            (by simpa [popped,payload] using input) (by simpa [popped] using source)
          have readyInput : ready 16 = payload rest := by rw [step]; exact first.1
          have readyFlag : ready 20 = if (flags[j-1]?).getD false then s 20 else [] := by
            rw [step,first.2]
            simp [popped]
          have result := ih rest ready tailPositive (by simpa using enough) readyInput readySource
          refine ⟨result.1,?_⟩
          rw [result.2,readyFlag]
          by_cases available : (flags[j-1]?).getD false <;> by_cases restAllowed : allowed flags rest <;>
            simp [allowed,available,restAllowed,firstPositive] at *

/-- The validation flag is exact for every well formed positive composition,
including the empty composition at zero. -/
theorem validationRoutine_value {O : Type} (flags : List Bool) (parts : Parts) (s : Store)
    (positive : ∀ j ∈ parts, 0 < j) (enough : parts.length ≤ (s 22).length)
    (input : s 31 = payload parts) (source : s 25 = flagsWord flags) :
    (validationRoutine (O := O)).eval s 20 = flagWord (allowed flags parts) := by
  let ready := (validationSetup (O := O)).eval s
  have readyInput : ready 16 = payload parts := by
    simp [ready,validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
      WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push,input]
  have readySource : ready 25 = flagsWord flags := by
    simpa [ready,validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
      WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push] using source
  have readyClock : (ready 18).length = (s 22).length := by
    simp [ready,validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
      WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push]
  have readyFlag : ready 20 = [Symbol.present] := by
    simp [ready,validationSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
      WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push]
  have result := counted_validation (O := O) flags parts (s 22).length ready positive enough readyInput readySource
  unfold validationRoutine validationLoop
  change ((WordStack.Routine.counted 18 (validationBody (O := O))).eval^[(ready 18).length] ready) 20 = _
  rw [readyClock,result.2,readyFlag]
  rfl

end ComplexityOfGenerators.Simulation.StarPaths
