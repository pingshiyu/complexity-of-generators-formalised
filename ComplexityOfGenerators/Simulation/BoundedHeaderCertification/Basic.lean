import ComplexityOfGenerators.Simulation.BoundedMachinePhase.Bounds
import ComplexityOfGenerators.Simulation.WordStack.OutputPrefix

/-! A capped productivity certificate returns an index header, discarding the
original bounded output. Existing finite union/concatenation selectors can then
retain the chosen source index without new selection machinery. -/
namespace ComplexityOfGenerators.Simulation.BoundedHeaderCertification
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

abbrev Cell := BoundedMachinePhase.Cell M
abbrev Store := Local.Store (Cell M) 35
abbrev Controller := WordStack.Routine (Cell M) Bool 35

def prepare : Controller M := (BoundedMachinePhase.prepare M).mapOutput (fun _ => false)
def trial (seed clock : PolynomialBound) : Controller M :=
  (UnionGenerator.leftTrial M M seed clock).mapOutput (fun _ => false)
def flag (value : Bool) : Controller M := (UnionGenerator.flag M M 32 value).mapOutput (fun _ => false)

def header (tag : Bool) : Controller M :=
  (Routine.assign 22 31 33 (by decide) (by decide) (by decide) (fun _ => Symbol.bit tag)).seq
    (Routine.ofLocal (Local.push 31 (Symbol.bit tag)))

def finish (tag : Bool) : Controller M :=
  Routine.branch 0 fun status => match status with
    | some (.left (.state .accepted)) => (header M tag).seq (flag M true)
    | _ => (Routine.clear 31).seq (flag M false)

def decode : Cell M → Option Bool
  | .bit b => some b
  | _ => none

noncomputable def phase (tag : Bool) (seed clock : PolynomialBound) : Controller M :=
  (prepare M).seq ((trial M seed clock).seq (finish M tag))

def value (tag : Bool) (clock : PolynomialBound) (n : ℕ) (bits : BitString) : Option (List Bool) :=
  (UnionGenerator.sourceValue M clock n bits).map (fun _ => List.replicate (n+1) tag)

@[simp] theorem flag_eval (value : Bool) (s : Store M) :
    (flag M value).eval s=Function.update s 32 (UnionGenerator.flagWord M M value) :=
  UnionGenerator.flag_eval M M 32 value s

@[simp] theorem header_eval (tag : Bool) (s : Store M) :
    (header M tag).eval s=Function.update (Function.update s 33 []) 31
      (List.replicate ((s 22).length+1) (Symbol.bit tag)) := by
  simp only [header,Routine.seq,Routine.assign_eval,Routine.ofLocal,Local.eval_push]
  rw [Function.update_self,List.map_const',← List.replicate_succ]
  exact Function.update_idem _ _ _

end
end ComplexityOfGenerators.Simulation.BoundedHeaderCertification
