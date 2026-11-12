import ComplexityOfGenerators.Simulation.StarCertification
import ComplexityOfGenerators.Simulation.StarPaths.Support
import ComplexityOfGenerators.Simulation.StarPaths.RandomFree
import ComplexityOfGenerators.Simulation.WordStack.CommandEmbedding

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
abbrev Cell := StarCertification.Cell M
abbrev Store := Local.Store (Cell M) 35
abbrev Step := WordStack.Routine (Cell M) α 35
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

def encodePath : StarPaths.Symbol → Cell M := Sum.inr

def projectPath : Cell M → StarPaths.Symbol
  | .inl _ => .unit
  | .inr value => value

def decodePath : Cell M → Option StarPaths.Symbol
  | .inl _ => none
  | .inr value => some value

@[simp] theorem project_encode (value : StarPaths.Symbol) : projectPath M (encodePath M value) = value := rfl
@[simp] theorem decode_encode (value : StarPaths.Symbol) : decodePath M (encodePath M value) = some value := rfl

def unitSymbol : Cell M := encodePath M .present
def bitSymbol (bit : Bool) : Cell M := encodePath M (StarPaths.coinSymbol bit)

/-- Normalize an input register through a scratch bank, preserving its order
and length, even on arbitrary initial global symbols. -/
def normalize (reg : Fin 35) (a : reg ≠ 33) (b : reg ≠ 34) (map : Cell M → Cell M) : Step M :=
  (WordStack.Routine.assign reg 34 33 b a (by decide) map).seq
    ((WordStack.Routine.assign 34 reg 33 b.symm (by decide) a id).seq (WordStack.Routine.clear 34))

theorem normalize_eval (reg : Fin 35) (a : reg ≠ 33) (b : reg ≠ 34) (map : Cell M → Cell M) (s : Store M) :
    (normalize M reg a b map).eval s = Function.update (Function.update (Function.update s 33 []) reg ((s reg).map map)) 34 [] := by
  funext j
  by_cases x : j = 33 <;> by_cases y : j = reg <;> by_cases z : j = 34 <;>
    simp [normalize,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.clear,x,y,z,a,b,b.symm,a.symm]

def canonicalPrepare : Step M := (WordStack.Routine.clearMany StarPaths.owned).seq
  ((normalize M 17 (by decide) (by decide) (fun value => encodePath M (projectPath M value))).seq
    ((normalize M 25 (by decide) (by decide) (fun value => encodePath M (projectPath M value))).seq
      (normalize M 22 (by decide) (by decide) (fun _ => unitSymbol M))))

def pathInput (s : Store M) : StarPaths.Store := fun j =>
  if j = 17 then (s 17).map (projectPath M)
  else if j = 22 then List.replicate (s 22).length .present
  else if j = 25 then (s 25).map (projectPath M) else []

/-- Every owned stack is now in the right-hand path alphabet. This is the
precondition needed by the proved command alphabet embedding. -/
theorem canonicalPrepare_eval (s : Store M) :
    (canonicalPrepare M).eval s = Local.mapStore (encodePath M) (pathInput M s) := by
  funext j
  by_cases a : j = 17 <;> by_cases b : j = 22 <;> by_cases c : j = 25 <;>
    simp [canonicalPrepare,WordStack.Routine.seq,WordStack.Routine.clearMany_eval,StarPaths.owned,
      normalize_eval,pathInput,Local.mapStore,a,b,c,List.map_map,Function.comp_def,unitSymbol,encodePath]
  by_cases d : j = 33 <;> by_cases e : j = 34 <;> simp [a,b,c,d,e]

end ComplexityOfGenerators.Simulation.CertifiedStarPhase
