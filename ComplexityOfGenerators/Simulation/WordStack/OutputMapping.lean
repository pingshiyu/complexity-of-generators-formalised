import ComplexityOfGenerators.Simulation.WordStack.Commands

/-! Retyping physical emissions preserves every stack instruction, consumed
coin, read-only head, and exact command cost. -/
namespace ComplexityOfGenerators.Simulation.WordStack

namespace Memory
variable {S O O' : Type} {k : ℕ}
def mapOutput (f : O → O') (m : Memory S O k) : Memory S O' k :=
  ⟨m.state,m.indexHead,m.randomHead,m.output.map f,m.store⟩
end Memory

namespace Result
variable {S O O' : Type} {k : ℕ}
def mapOutput (f : O → O') : Result S O k → Result S O' k
  | .exhausted => .exhausted
  | .done m => .done (m.mapOutput f)
end Result

namespace Command
variable {S O O' : Type} {k : ℕ}
def mapOutput (f : O → O') : Command S O k → Command S O' k
  | .skip => .skip
  | .act j action index emit => .act j action index (emit.map f)
  | .branch j next => .branch j (fun observation => (next observation).mapOutput f)
  | .random no yes => .random (no.mapOutput f) (yes.mapOutput f)
  | .seq first second => .seq (first.mapOutput f) (second.mapOutput f)
  | .loop j test body => .loop j test (body.mapOutput f)
  | .drain => .drain

private theorem changeMemory_mapOutput (f : O → O') (j : Fin k) (n : ℕ)
    (action : Action S) (index : Move) (emit : Option O) (m : Memory S O k) :
    (Program.changeMemory j n action index emit m).mapOutput f =
      Program.changeMemory j n action index (emit.map f) (m.mapOutput f) := by
  cases emit <;> simp [Program.changeMemory,Memory.mapOutput,List.map_append]

/-- Output mapping does not change the number of primitive stack steps. -/
theorem Runs.mapOutput (f : O → O') {n : ℕ} {bits : BitString} {c : Command S O k}
    {m : Memory S O k} {ticks : ℕ} {result : Result S O k}
    (run : c.Runs n bits m ticks result) :
    (c.mapOutput f).Runs n bits (m.mapOutput f) ticks (result.mapOutput f) := by
  induction run with
  | skip m => exact .skip _
  | act m j action index emit =>
      simpa only [Command.mapOutput,Result.mapOutput,changeMemory_mapOutput] using
        Runs.act (m.mapOutput f) j action index (emit.map f)
  | branch m j next t result run ih => exact .branch _ _ _ _ _ ih
  | random_absent m no yes absent => exact .random_absent _ _ _ absent
  | random m no yes bit t result lookup run ih =>
      change Runs n bits (.random (no.mapOutput f) (yes.mapOutput f)) (m.mapOutput f) (1+t) _
      apply Runs.random (m.mapOutput f) (no.mapOutput f) (yes.mapOutput f) bit _ _ lookup
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
end ComplexityOfGenerators.Simulation.WordStack
