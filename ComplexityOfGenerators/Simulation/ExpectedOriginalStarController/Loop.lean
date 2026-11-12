import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Call

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

/-- A factor-by-factor decomposition retains the exact memory just before
each native event. It contains actual command executions, not an assumed
source-call implementation. -/
inductive Trace (n : ℕ) (bits : BitString) :
    List ℕ → Memory (Cell M) Unit 80 → Memory (Cell M) Unit 80 → Prop
  | nil (m) : Trace n bits [] m m
  | cons (j parts m finish ticks)
      (prepared : (prepareFactor M).command.Runs n bits m ticks (.done (afterFactor M m)))
      (ready : EventReady M j parts (afterFactor M m))
      (rest : Trace n bits parts (afterEvent M (afterFactor M m)) finish) :
      Trace n bits (j::parts) m finish

theorem loop_runs (n : ℕ) (bits : BitString) (parts : List ℕ)
    (m : Memory (Cell M) Unit 80) (budget : ℕ) (origin : m.indexHead=0)
    (path : m.store 31=pathWord M parts) (zero : m.store 0=[])
    (sizes : StoreBound m.store budget) :
    ∃ ticks≤16*(budget+1)*parts.length, ∃ next,
      (loop M).Runs n bits m ticks (.done next) ∧
      next.indexHead=0 ∧ next.randomHead=m.randomHead ∧
      next.output=m.output++List.replicate parts.length () ∧
      next.store 31=[] ∧ next.store 0=[] ∧ StoreBound next.store budget ∧
      Trace M n bits parts m next := by
  induction parts generalizing m with
  | nil =>
      refine ⟨0,by simp,m,?_,origin,rfl,by simp,by simpa using path,zero,sizes,.nil m⟩
      apply Command.Runs.loop_stop
      simp [observe,path]
  | cons j parts ih =>
      obtain ⟨s,firstBound,prepareRun,ready,afterBound⟩ :=
        prepareFactor_runs M n bits m budget j parts origin path zero sizes
      let middle := afterEvent M (afterFactor M m)
      have first : (call M).Runs n bits m (s+1+1) (.done middle) :=
        Command.Runs.seq _ _ _ _ _ _ _ prepareRun (event_runs M n bits _ ready.origin)
      have middleOrigin : middle.indexHead=0 := ready.origin
      have middlePath : middle.store 31=pathWord M parts := ready.path
      have middleZero : middle.store 0=[] := ready.eventRegister
      obtain ⟨t,restBound,next,restRun,nextOrigin,nextRandom,nextOutput,nextPath,nextZero,nextBound,trace⟩ :=
        ih middle middleOrigin middlePath middleZero afterBound
      refine ⟨1+(s+1+1)+1+t,?_,next,?_,nextOrigin,nextRandom,?_,nextPath,nextZero,nextBound,
        .cons j parts m next s prepareRun ready trace⟩
      · rw [List.length_cons,Nat.mul_succ (16*(budget+1)) parts.length]
        omega
      · apply Command.Runs.loop _ middle _ _ _ _ _ _ ?_ first restRun
        simp [observe,path,pathWord_cons]
      · rw [nextOutput]
        simp [middle,afterEvent,afterFactor,List.replicate_succ,List.append_assoc]

theorem events_runs (n : ℕ) (bits : BitString) (parts : List ℕ)
    (m : Memory (Cell M) Unit 80) (budget : ℕ) (origin : m.indexHead=0)
    (path : m.store 31=pathWord M parts) (sizes : StoreBound m.store budget) :
    ∃ ticks≤20*(budget+1)*(parts.length+1), ∃ next,
      (events M).Runs n bits m ticks (.done next) ∧
      next.indexHead=0 ∧ next.randomHead=m.randomHead ∧
      next.output=m.output++List.replicate parts.length () ∧
      next.store 31=[] ∧ next.store 0=[] ∧ StoreBound next.store budget ∧
      Trace M n bits parts (m.set 0 []) next := by
  have clear := Command.clear_runs (n := n) (0 : Fin 80) bits m (by omega)
  have cleanSizes : StoreBound (m.set 0 []).store budget := sizes.clear 0
  have cleanPath : (m.set 0 []).store 31=pathWord M parts := by simpa [Memory.set] using path
  obtain ⟨ticks,bound,next,run,nextOrigin,nextRandom,nextOutput,nextPath,nextZero,nextBound,trace⟩ :=
    loop_runs M n bits parts (m.set 0 []) budget origin cleanPath (by simp) cleanSizes
  refine ⟨3*(m.store 0).length+1+ticks,?_,next,
    Command.Runs.seq _ _ _ _ _ _ _ clear run,nextOrigin,nextRandom,nextOutput,nextPath,nextZero,nextBound,trace⟩
  have zeroBound := sizes 0
  rw [Nat.mul_succ (20*(budget+1)) parts.length]
  have scale : 16*(budget+1)*parts.length≤20*(budget+1)*parts.length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
