import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.WordStack.Routine

variable {S O : Type} {k : ℕ}

def guardedOutput (flag output : Fin k) (body : Routine S O k) : Routine S O k :=
  branch flag fun ready => if ready.isSome then body else clear output

theorem guardedOutput_value (flag output : Fin k) (body : Routine S O k) (s : Local.Store S k) :
    (guardedOutput flag output body).eval s output =
      if (s flag).head?.isSome then body.eval s output else [] := by
  simp only [guardedOutput, branch]
  split <;> simp [clear]

theorem guardedOutput_bound (flag output : Fin k) (body : Routine S O k) (s : Local.Store S k)
    (budget cap time : ℕ) (sizes : StoreBound s budget) (room : budget ≤ cap)
    (bounded : StoreBound (body.eval s) cap) (cost : body.cost s ≤ time) :
    StoreBound ((guardedOutput flag output body).eval s) cap ∧
      (guardedOutput flag output body).cost s ≤ time + 3 * budget + 1 := by
  simp only [guardedOutput, branch]
  split
  · exact ⟨bounded, by omega⟩
  · exact ⟨(sizes.mono room).clear output, by change 1 + 3 * (s output).length ≤ _; have := sizes output; omega⟩

theorem guardedOutput_randomFree (flag output : Fin k) (body : Routine S O k)
    (pure : Command.RandomFree body.command) : Command.RandomFree (guardedOutput flag output body).command := by
  simp only [guardedOutput, randomFree_branch]
  intro ready
  split
  · exact pure
  · exact randomFree_clear _

end ComplexityOfGenerators.Simulation.WordStack.Routine
