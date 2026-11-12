import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.Cycle
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.BoundedResult

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
open BinaryCounter
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ}

/-- Every choice tape gives a bounded actual execution. The source's uniform
space invariant supplies the same region throughout the clocked simulation. -/
theorem execution (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (canonical : Canonical digits) (c : BankConfiguration O Q S k)
    (radius : ℕ)
    (allBound : ∀ ticks finish, source.Steps data choices c ticks finish → source.Bounded data radius finish) :
    ∃ time, time≤FixedBitBlocks.decode digits*(2*digits.length+8) ∧
      (bank source).Executes data choices (configuration source digits c .check) time
        (boundedResult source data choices (FixedBitBlocks.decode digits) c) ∧
      (bank source).RegionRun data choices (radius+2*digits.length+4)
        (configuration source digits c .check) (boundedResult source data choices (FixedBitBlocks.decode digits) c) := by
  generalize value : FixedBitBlocks.decode digits=fuel
  induction fuel generalizing digits c with
  | zero =>
    have empty : digits=[] := by
      by_contra nonempty
      have positive := canonical_value_positive digits canonical nonempty
      omega
    subst digits
    have bounded := configuration_bounded source data [] c .check radius (allBound 0 c (.refl _))
    have table : (bank source).instruction data (configuration source [] c .check)=.reject := by
      simp [TapeBank.instruction,bank,configuration,transition,digitTape]
    exact ⟨0,by simp,.reject _ table,0,_,.refl _ (bounded.mono (bank source) (by omega)),.reject _ table⟩
  | succ fuel ih =>
    have nonempty : digits≠[] := by intro empty;simp [empty,FixedBitBlocks.decode] at value
    have decremented : FixedBitBlocks.decode (decrement digits)=fuel := by
      rw [decrement_value digits canonical,value]
      omega
    have bounded := allBound 0 c (.refl _)
    obtain ⟨cycleTime,cycleCost,cycle⟩ := cycle_path source data choices digits canonical nonempty c radius bounded
    have terminalCost : cycleTime≤(fuel+1)*(2*digits.length+8) := by nlinarith
    cases table : source.instruction data c with
    | accept =>
      have halt : (bank source).Executes data choices (configuration source (decrement digits) c .source) 0
          (.accepted c.output) := by
        apply TapeBank.Executes.accept
        rw [source_instruction,table]
        rfl
      refine ⟨cycleTime,terminalCost,?_,?_⟩
      · simpa [boundedResult,table] using cycle.toSteps (bank source) |>.executes (bank source) halt
      · simpa [boundedResult,table] using (show (bank source).RegionRun data choices
          (radius+2*digits.length+4) (configuration source digits c .check) (.accepted c.output) from
          ⟨cycleTime,_,cycle,halt⟩)
    | reject =>
      have halt : (bank source).Executes data choices (configuration source (decrement digits) c .source) 0 .rejected := by
        apply TapeBank.Executes.reject
        rw [source_instruction,table]
        rfl
      refine ⟨cycleTime,terminalCost,?_,?_⟩
      · simpa [boundedResult,table] using cycle.toSteps (bank source) |>.executes (bank source) halt
      · simpa [boundedResult,table] using (show (bank source).RegionRun data choices
          (radius+2*digits.length+4) (configuration source digits c .check) .rejected from ⟨cycleTime,_,cycle,halt⟩)
    | readRandom no yes =>
      cases lookup : choices[c.randomHead]? with
      | none =>
        have halt : (bank source).Executes data choices (configuration source (decrement digits) c .source) 0 .exhausted := by
          apply TapeBank.Executes.exhausted _ (no,.check) (yes,.check)
          · rw [source_instruction,table];rfl
          · exact lookup
        refine ⟨cycleTime,terminalCost,?_,?_⟩
        · simpa [boundedResult,table,lookup] using cycle.toSteps (bank source) |>.executes (bank source) halt
        · simpa [boundedResult,table,lookup] using (show (bank source).RegionRun data choices
            (radius+2*digits.length+4) (configuration source digits c .check) .exhausted from ⟨cycleTime,_,cycle,halt⟩)
      | some bit =>
        let next := TapeBank.choose c (if bit then yes else no)
        have sourceStep : source.Steps data choices c 1 next :=
          .random c no yes bit 0 next table lookup (.refl _)
        have nextBound : source.Bounded data radius next := allBound 1 next sourceStep
        have nextAll : ∀ ticks finish, source.Steps data choices next ticks finish → source.Bounded data radius finish :=
          fun _ _ path => allBound _ _ (sourceStep.trans source path)
        obtain ⟨time,cost,run,region⟩ := ih (decrement digits) (decrement_canonical digits canonical) next nextAll decremented
        have enlarged : time≤fuel*(2*digits.length+8) := cost.trans
          (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (decrement_length digits)) 8))
        have stepTable : (bank source).instruction data (configuration source (decrement digits) c .source)=
            .readRandom (no,.check) (yes,.check) := by rw [source_instruction,table];rfl
        have chosen : TapeBank.choose (configuration source (decrement digits) c .source)
            (if bit then (yes,.check) else (no,.check))=configuration source (decrement digits) next .check := by
          cases bit <;> rfl
        have path : (bank source).RegionSteps data choices (radius+2*digits.length+4)
            (configuration source (decrement digits) c .source) 1
            (configuration source (decrement digits) next .check) := by
          apply TapeBank.RegionSteps.random _ (no,.check) (yes,.check) bit 0 _
            ((configuration_bounded source data _ c .source radius bounded).mono (bank source) (by omega)) stepTable lookup
          rw [chosen]
          exact .refl _ ((configuration_bounded source data _ next .check radius nextBound).mono (bank source) (by omega))
        have sourceRun : (bank source).Executes data choices (configuration source (decrement digits) c .source) (time+1)
            (boundedResult source data choices fuel next) := by
          apply TapeBank.Executes.random _ (no,.check) (yes,.check) bit time _ stepTable lookup
          rw [chosen]
          exact run
        refine ⟨cycleTime+(time+1),by nlinarith,?_,?_⟩
        · simpa [boundedResult,table,lookup,next] using (cycle.toSteps (bank source)).executes (bank source) sourceRun
        · have widened := region.mono (bank source) (show radius+2*(decrement digits).length+4≤radius+2*digits.length+4 by
            have length := decrement_length digits;omega)
          simpa [boundedResult,table,lookup,next] using (widened.prepend (bank source) path).prepend (bank source) cycle
    | step next write work input auxiliary index emit =>
      let after := source.advance data c next write work input auxiliary index emit
      have sourceStep : source.Steps data choices c 1 after :=
        .step c next write work input auxiliary index emit 0 after table (.refl _)
      have afterBound : source.Bounded data radius after := allBound 1 after sourceStep
      have afterAll : ∀ ticks finish, source.Steps data choices after ticks finish → source.Bounded data radius finish :=
        fun _ _ path => allBound _ _ (sourceStep.trans source path)
      obtain ⟨time,cost,run,region⟩ := ih (decrement digits) (decrement_canonical digits canonical) after afterAll decremented
      have enlarged : time≤fuel*(2*digits.length+8) := cost.trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (decrement_length digits)) 8))
      have stepTable : (bank source).instruction data (configuration source (decrement digits) c .source)=
          .step (next,.check) (write,none) work input auxiliary index emit := by rw [source_instruction,table];rfl
      have path : (bank source).RegionSteps data choices (radius+2*digits.length+4)
          (configuration source (decrement digits) c .source) 1 (configuration source (decrement digits) after .check) := by
        apply TapeBank.RegionSteps.step _ (next,.check) (write,none) work input auxiliary index emit 0 _
          ((configuration_bounded source data _ c .source radius bounded).mono (bank source) (by omega)) stepTable
        rw [source_advance]
        exact .refl _ ((configuration_bounded source data _ after .check radius afterBound).mono (bank source) (by omega))
      have sourceRun : (bank source).Executes data choices (configuration source (decrement digits) c .source) (time+1)
          (boundedResult source data choices fuel after) := by
        apply TapeBank.Executes.step _ (next,.check) (write,none) work input auxiliary index emit time _ stepTable
        rw [source_advance]
        exact run
      refine ⟨cycleTime+(time+1),by nlinarith,?_,?_⟩
      · simpa [boundedResult,table,after] using (cycle.toSteps (bank source)).executes (bank source) sourceRun
      · have widened := region.mono (bank source) (show radius+2*(decrement digits).length+4≤radius+2*digits.length+4 by
          have length := decrement_length digits;omega)
        simpa [boundedResult,table,after] using (widened.prepend (bank source) path).prepend (bank source) cycle

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
