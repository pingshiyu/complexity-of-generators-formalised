import ComplexityOfGenerators.Simulation.WordStack.OutputMapping

namespace ComplexityOfGenerators.Simulation.WordStack
namespace Memory
variable {S O O' : Type} {k : ℕ}
def filterMapOutput (f : O→Option O') (m : Memory S O k) : Memory S O' k :=
  ⟨m.state,m.indexHead,m.randomHead,m.output.filterMap f,m.store⟩
end Memory
namespace Result
variable {S O O' : Type} {k : ℕ}
def filterMapOutput (f : O→Option O') : Result S O k→Result S O' k
  | .exhausted => .exhausted
  | .done m => .done (m.filterMapOutput f)
end Result
namespace Command
variable {S O O' : Type} {k : ℕ}
def filterMapOutput (f : O→Option O') : Command S O k→Command S O' k
  | .skip => .skip
  | .act j action index emit => .act j action index (emit.bind f)
  | .branch j next => .branch j (fun observation=>(next observation).filterMapOutput f)
  | .random no yes => .random (no.filterMapOutput f) (yes.filterMapOutput f)
  | .seq first second => .seq (first.filterMapOutput f) (second.filterMapOutput f)
  | .loop j test body => .loop j test (body.filterMapOutput f)
  | .drain => .drain

private theorem changeMemory_filterMapOutput (f : O→Option O') (j : Fin k) (n : ℕ)
    (action : Action S) (index : Move) (emit : Option O) (m : Memory S O k) :
    (Program.changeMemory j n action index emit m).filterMapOutput f =
      Program.changeMemory j n action index (emit.bind f) (m.filterMapOutput f) := by
  cases emit with
  | none => simp [Program.changeMemory,Memory.filterMapOutput]
  | some letter => cases output : f letter <;>
      simp [Program.changeMemory,Memory.filterMapOutput,List.filterMap_append,output]

theorem Runs.filterMapOutput (f : O→Option O') {n : ℕ} {bits : BitString} {c : Command S O k}
    {m : Memory S O k} {ticks : ℕ} {result : Result S O k}
    (run : c.Runs n bits m ticks result) :
    (c.filterMapOutput f).Runs n bits (m.filterMapOutput f) ticks (result.filterMapOutput f) := by
  induction run with
  | skip m => exact .skip _
  | act m j action index emit =>
      simpa only [Command.filterMapOutput,Result.filterMapOutput,changeMemory_filterMapOutput] using
        Runs.act (m.filterMapOutput f) j action index (emit.bind f)
  | branch m j next t result run ih => exact .branch _ _ _ _ _ ih
  | random_absent m no yes absent => exact .random_absent _ _ _ absent
  | random m no yes bit t result lookup run ih =>
      change Runs n bits (.random (no.filterMapOutput f) (yes.filterMapOutput f)) (m.filterMapOutput f) (1+t) _
      apply Runs.random (m.filterMapOutput f) (no.filterMapOutput f) (yes.filterMapOutput f) bit _ _ lookup
      cases bit <;> exact ih
  | seq_absent m first second t run ih => exact .seq_absent _ _ _ _ ih
  | seq m middle first second s t result left right ihLeft ihRight => exact .seq _ _ _ _ _ _ _ ihLeft ihRight
  | loop_stop m j test body stop => exact .loop_stop _ _ _ _ stop
  | loop_absent m j test body t again run ih => exact .loop_absent _ _ _ _ _ again ih
  | loop m middle j test body s t result again run rest ihBody ihRest =>
      exact .loop _ _ _ _ _ _ _ _ again ihBody ihRest
  | drain m => exact .drain _

end Command
end ComplexityOfGenerators.Simulation.WordStack
