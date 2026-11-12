import ComplexityOfGenerators.Simulation.WordStack.OutputMapping
import ComplexityOfGenerators.Simulation.WordStack.Routines

/-! Output prefixes do not affect primitive controller instructions. This
extends output mapping to routines without duplicating their execution proofs. -/
namespace ComplexityOfGenerators.Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Memory
variable {S O : Type} {k : ℕ}
def prefixOutput (past : List O) (m : Memory S O k) : Memory S O k :=
  {m with output:=past++m.output}
end Memory
namespace Result
variable {S O : Type} {k : ℕ}
def prefixOutput (past : List O) : Result S O k → Result S O k
  | .exhausted => .exhausted
  | .done m => .done (m.prefixOutput past)
end Result
namespace Command
variable {S O : Type} {k : ℕ}
private theorem changeMemory_prefixOutput (past : List O) (j : Fin k) (n : ℕ)
    (action : Action S) (index : Move) (emit : Option O) (m : Memory S O k) :
    (Program.changeMemory j n action index emit m).prefixOutput past =
      Program.changeMemory j n action index emit (m.prefixOutput past) := by
  cases emit <;> simp [Program.changeMemory,Memory.prefixOutput,List.append_assoc]

theorem Runs.prefixOutput (past : List O) {n : ℕ} {bits : BitString} {c : Command S O k}
    {m : Memory S O k} {ticks : ℕ} {result : Result S O k}
    (run : c.Runs n bits m ticks result) :
    c.Runs n bits (m.prefixOutput past) ticks (result.prefixOutput past) := by
  induction run with
  | skip m => exact .skip _
  | act m j action index emit =>
      simpa only [Result.prefixOutput,changeMemory_prefixOutput] using
        Runs.act (m.prefixOutput past) j action index emit
  | branch m j next t result run ih => exact .branch _ _ _ _ _ ih
  | random_absent m no yes absent => exact .random_absent _ _ _ absent
  | random m no yes bit t result lookup run ih =>
      apply Runs.random (m.prefixOutput past) no yes bit t (result.prefixOutput past) lookup
      cases bit <;> exact ih
  | seq_absent m first second t run ih => exact .seq_absent _ _ _ _ ih
  | seq m middle first second s t result left right ihLeft ihRight =>
      exact .seq _ _ _ _ _ _ _ ihLeft ihRight
  | loop_stop m j test body stop => exact .loop_stop _ _ _ _ stop
  | loop_absent m j test body t again run ih => exact .loop_absent _ _ _ _ _ again ih
  | loop m middle j test body s t result again run rest ihBody ihRest =>
      exact .loop _ _ _ _ _ _ _ _ again ihBody ihRest
  | drain m => exact .drain _
end Command

namespace Routine
variable {S O P : Type} {k : ℕ}
/-- A routine preserves its caller's output. Mapping its output type therefore
preserves arbitrary prefixes and its exact primitive cost bound. -/
def mapOutput (f : O → P) (routine : Routine S O k) : Routine S P k where
  command := routine.command.mapOutput f
  eval := routine.eval
  cost := routine.cost
  runs bits m bounded := by
    let start : Memory S O k := ⟨(),m.indexHead,m.randomHead,[],m.store⟩
    obtain ⟨ticks,cost,run⟩ := routine.runs bits start bounded
    refine ⟨ticks,cost,?_⟩
    have mapped := (run.mapOutput f).prefixOutput m.output
    simpa only [start,Memory.mapOutput,Memory.prefixOutput,Result.mapOutput,Result.prefixOutput,
      List.map_nil,List.append_nil] using mapped
end Routine
end
end ComplexityOfGenerators.Simulation.WordStack
