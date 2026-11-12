import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Prepare
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Correctness

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem emit_runs (source : Fin 64) {n : ℕ} (bits : BitString) (m : Memory) (index : m.indexHead≤n) :
    ∃ final, (emit source).Runs n bits m (4*(m.store source).length) (.done final) ∧
      final.output=m.output++m.store source := by
  refine ⟨Command.emitted source some m,Command.emitWord_runs source some bits m index,?_⟩
  simp [Command.emitted]

theorem finish_dead {n : ℕ} (bits : BitString) (m : Memory)
    (dead : (m.store 41).head?.isSome=false) :
    finish.Runs n bits m (1+(bits.length-m.randomHead)) .exhausted := by
  apply Command.Runs.branch
  simpa only [observe,dead,Bool.false_eq_true,ite_false] using
    (Command.Runs.drain (n := n) (bits := bits) m)

noncomputable def finishBudget (s : Store) : ℕ :=
  (Output.routine (O := Symbol)).cost s+4*((Output.routine (O := Symbol)).eval s 31).length+2

theorem finish_live {n : ℕ} (bits : BitString) (m : Memory) (index : m.indexHead≤n)
    (live : (m.store 41).head?.isSome=true) :
    ∃ ticks≤finishBudget m.store, ∃ final,
      finish.Runs n bits m ticks (.done final) ∧
        final.output=m.output++(Output.routine (O := Symbol)).eval m.store 31 := by
  let after : Memory := {m with store := (Output.routine (O := Symbol)).eval m.store}
  obtain ⟨ticks,cost,run⟩ := (Output.routine (O := Symbol)).runs bits m index
  obtain ⟨final,outputRun,output⟩ := emit_runs 31 bits after index
  have both := Command.Runs.seq _ _ _ _ _ _ _ run outputRun
  have finished : finish.Runs n bits m
      (1+(ticks+1+4*((Output.routine (O := Symbol)).eval m.store 31).length)) (.done final) := by
    apply Command.Runs.branch
    simpa only [observe,live,ite_true,after] using both
  refine ⟨1+(ticks+1+4*((Output.routine (O := Symbol)).eval m.store 31).length),?_,final,finished,output⟩
  unfold finishBudget
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
