import ComplexityOfGenerators.Examples.HAMPATHNative.Parser

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def acceptedSyntax (s : Store) : Bool :=
  (s 6).head?.isSome && (s 12).head?.isSome && (s 2).isEmpty

def markSyntax : Local Symbol 32 :=
  .read 6 fun valid => if valid.isSome then
    .read 12 fun seen => if seen.isSome then
      .read 2 fun remaining => if remaining.isSome then .skip else Local.push 16 (.bit true)
    else .skip
  else .skip

def metadata {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 16).seq ((Routine.ofLocal markSyntax).seq
    (Routine.assign 4 17 18 (by decide) (by decide) (by decide) (fun _ => .bit true)))

theorem metadata_eval {O : Type} (s : Store) :
    (metadata (O := O)).eval s = Function.update (Function.update (Function.update s
      16 (flag (acceptedSyntax s))) 18 []) 17 (List.replicate (s 4).length (.bit true)) := by
  cases valid : s 6 <;> cases seen : s 12 <;> cases remaining : s 2 <;> funext j <;>
    simp [metadata, markSyntax, acceptedSyntax, flag, Routine.seq, Routine.clear, Routine.ofLocal,
      Routine.assign_eval, Local.eval, Local.push, Action.apply, valid, seen, remaining, List.map_const']

def gate {O : Type} (output : Fin 32) : Routine Symbol O 32 :=
  Routine.branch 16 fun valid => if valid.isSome then Routine.skip else Routine.clear output

theorem gate_eval {O : Type} (output : Fin 32) (s : Store) :
    (gate (O := O) output).eval s output = if (s 16).head?.isSome then s output else [] := by
  simp only [gate, Routine.branch]
  split <;> simp [Routine.skip, Routine.ofLocal, Routine.clear]

theorem gate_cost {O : Type} (output : Fin 32) (s : Store) :
    (gate (O := O) output).cost s ≤ 3 * (s output).length + 1 := by
  simp only [gate, Routine.branch]
  split <;> simp [Routine.skip, Routine.ofLocal, Local.ticks, Routine.clear] <;> omega

theorem metadata_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (metadata (O := O)).cost s ≤ 40 * (budget + 1) := by
  have source := sizes 4
  have saved := sizes 16
  have output := sizes 17
  have scratch := sizes 18
  have marking : markSyntax.ticks ((Routine.clear (O := O) 16).eval s) ≤ 4 := by
    cases valid : s 6 <;> cases seen : s 12 <;> cases remaining : s 2 <;>
      simp [markSyntax, Local.ticks, Local.push, Routine.clear, valid, seen, remaining]
  have stable4 : markSyntax.eval ((Routine.clear (O := O) 16).eval s) 4 = s 4 := by
    cases valid : s 6 <;> cases seen : s 12 <;> cases remaining : s 2 <;>
      simp [markSyntax, Local.eval, Local.push, Action.apply, Routine.clear, valid, seen, remaining]
  have stable17 : markSyntax.eval ((Routine.clear (O := O) 16).eval s) 17 = s 17 := by
    cases valid : s 6 <;> cases seen : s 12 <;> cases remaining : s 2 <;>
      simp [markSyntax, Local.eval, Local.push, Action.apply, Routine.clear, valid, seen, remaining]
  have stable18 : markSyntax.eval ((Routine.clear (O := O) 16).eval s) 18 = s 18 := by
    cases valid : s 6 <;> cases seen : s 12 <;> cases remaining : s 2 <;>
      simp [markSyntax, Local.eval, Local.push, Action.apply, Routine.clear, valid, seen, remaining]
  change 3 * (s 16).length + 1 + (markSyntax.ticks ((Routine.clear (O := O) 16).eval s) + 1 + _) ≤ _
  rw [Routine.assign_cost]
  simp only [Routine.ofLocal]
  rw [stable4, stable17, stable18]
  omega

theorem metadata_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget)
    (sizes : ∀ j, (s j).length ≤ budget) : ∀ j, ((metadata (O := O)).eval s j).length ≤ budget := by
  intro j
  rw [metadata_eval]
  by_cases saved : j = 16 <;> by_cases output : j = 17 <;> by_cases scratch : j = 18 <;>
    simp [Function.update_apply, saved, output, scratch, flag] <;>
    (try split) <;> simp_all

theorem metadata_randomFree {O : Type} : Command.RandomFree (metadata (O := O)).command := by simp [metadata]

theorem gate_randomFree {O : Type} (output : Fin 32) : Command.RandomFree (gate (O := O) output).command := by
  simp only [gate, Routine.randomFree_branch]
  intro valid
  split <;> simp

end ComplexityOfGenerators.Examples.HAMPATH.Native
