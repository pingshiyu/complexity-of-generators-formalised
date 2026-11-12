import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.State

namespace ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O) (parameter : F → Bool)

/-- Only the fixed caller track determines the unary parameter. -/
def Unary (fixed : ℤ → F) (length : ℕ) : Prop :=
  ∀ p : ℕ, parameter (fixed p) = decide (p<length)

theorem scan (data : InputData Unit Bool) (bits : BitString) (fixed : ℤ → F)
    (length remaining count : ℕ) (equation : length=count+remaining) (positive : 0<count)
    (unary : Unary parameter fixed length) (c : Configuration (machine M parameter))
    (represented : State M parameter data fixed {0} (packetPrefix length count) .scan count c) :
    ∃ d, State M parameter data fixed {0} (packet length 0 0) .rewind length d ∧
      (machine M parameter).Steps data bits c (remaining+1) d ∧
      WorkFrame (machine M parameter) c d := by
  induction remaining generalizing count c with
  | zero =>
      have same : count=length := by omega
      have live : parameter (fixed count)=false := by rw [unary count]; simp [same]
      have cell := represented.memory (count : ℤ)
      have table : transition M parameter .scan (c.work c.workHead) =
          .step (control .rewind)
            (some (alphabet M {read M (c.work c.workHead) with
              packet := some ⟨false,true,false⟩})) .stay .stay .stay .stay none := by
        simp only [represented.head, cell, transition, live, Bool.not_false, Bool.false_eq_true,
          ite_false]
      obtain ⟨d, result, path, frame⟩ := represented.packetStep bits .rewind
        (some ⟨false,true,false⟩) .stay table
      have update : Function.update (packetPrefix length count) (count : ℤ)
          (some ⟨false,true,false⟩) = packet length 0 0 := by
        have nonzero : length≠0 := by omega
        simpa [same, nonzero, packetPrefix_complete] using packetPrefix_write length count (by omega)
      rw [update] at result
      exact ⟨d, by simpa [Move.onInt, same] using result, path, frame⟩
  | succ remaining ih =>
      have inside : count<length := by omega
      have live : parameter (fixed count)=true := by simp [unary count, inside]
      have cell := represented.memory (count : ℤ)
      have table : transition M parameter .scan (c.work c.workHead) =
          .step (control .scan)
            (some (alphabet M {read M (c.work c.workHead) with
              packet := some ⟨false,false,false⟩})) .right .stay .stay .stay none := by
        simp only [represented.head, cell, transition, live, Bool.not_true, ite_true]
      obtain ⟨middle, middleState, first, firstFrame⟩ := represented.packetStep bits .scan
        (some ⟨false,false,false⟩) .right table
      have update : Function.update (packetPrefix length count) (count : ℤ)
          (some ⟨false,false,false⟩) = packetPrefix length (count+1) := by
        have nonzero : count≠0 := by omega
        have different : count≠length := by omega
        simpa [nonzero,different] using packetPrefix_write length count (by omega)
      rw [update] at middleState
      have atNext : State M parameter data fixed {0} (packetPrefix length (count+1))
          .scan (count+1) middle := by
        simpa [Move.onInt, Nat.cast_add, Nat.cast_one] using middleState
      obtain ⟨d, result, rest, restFrame⟩ := ih (count+1) (by omega) (by omega) middle atNext
      refine ⟨d,result,?_,WorkFrame.trans (machine M parameter) firstFrame restFrame⟩
      convert Machine.Steps.trans (machine M parameter) first rest using 1 <;> omega

theorem rewind (data : InputData Unit Bool) (bits : BitString) (fixed : ℤ → F)
    (length position : ℕ) (c : Configuration (machine M parameter))
    (represented : State M parameter data fixed {0} (packet length 0 0) .rewind position c) :
    ∃ d, State M parameter data fixed {0} (packet length 0 0) .done 0 d ∧
      (machine M parameter).Steps data bits c (position+1) d ∧
      WorkFrame (machine M parameter) c d := by
  induction position generalizing c with
  | zero =>
      have cell := represented.memory 0
      have table : transition M parameter .rewind (c.work c.workHead) =
          .step (control .done) none .stay .stay .stay .stay none := by
        simp [represented.head, cell, transition]
      obtain ⟨d,result,path,frame⟩ := represented.silent bits .done .stay table
      exact ⟨d,by simpa [Move.onInt] using result,path,frame⟩
  | succ position ih =>
      have cell := represented.memory (position+1 : ℕ)
      have notFirst : (packet length 0 0 (position+1 : ℕ)).any IndexMark.first=false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        have equality := (packet_first_iff length 0 0 (position+1 : ℕ)).mp yes
        omega
      have table : transition M parameter .rewind (c.work c.workHead) =
          .step (control .rewind) none .left .stay .stay .stay none := by
        simp only [represented.head, cell, transition, notFirst, Bool.false_eq_true, ite_false]
      obtain ⟨middle,middleState,first,firstFrame⟩ := represented.silent bits .rewind .left table
      have atPrevious : State M parameter data fixed {0} (packet length 0 0) .rewind position middle := by
        simpa [Move.onInt, Nat.cast_add, Nat.cast_one] using middleState
      obtain ⟨d,result,rest,restFrame⟩ := ih middle atPrevious
      refine ⟨d,result,?_,WorkFrame.trans (machine M parameter) firstFrame restFrame⟩
      convert Machine.Steps.trans (machine M parameter) first rest using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
