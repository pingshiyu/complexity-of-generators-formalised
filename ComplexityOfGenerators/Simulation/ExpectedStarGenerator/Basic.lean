import ComplexityOfGenerators.Simulation.CertifiedStarPhase
import ComplexityOfGenerators.Simulation.ExpectedStarCalls
import ComplexityOfGenerators.Simulation.WordStack.ReadOnlyRewind

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

abbrev Outer := CertifiedStarPhase.Cell M
abbrev Cell := ExpectedStarCalls.Cell (β := Outer M) P
abbrev Store := Local.Store (Cell M P) 80
abbrev Controller := WordStack.Routine (Cell M P) α 80

def outerSlots : Fin 35 ↪ Fin 80 where
  toFun i := ⟨i.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun k : Fin 80 => k.val) same)

def outerDecode : Cell M P → Outer M := Sum.elim id (fun _ => CertifiedStarPhase.unitSymbol M)

def unitSymbol : Cell M P := .inl (CertifiedStarPhase.unitSymbol M)

def setup : Controller M P :=
  (Routine.assign 13 22 33 (by decide) (by decide) (by decide) id).seq
    ((Routine.clear 31).seq ((Routine.clear 32).seq
      (Routine.assign 13 75 76 (by decide) (by decide) (by decide) id)))

/-- Load the generator index once, then rewind its actual read-only head.
Every subsequent source-phase call uses its own stored smaller index. -/
def boot : Command (Cell M P) α 80 :=
  (Command.loadIndex 13 (unitSymbol M P)).seq ((setup M P).command.seq (Command.rewind 75))

noncomputable def pathRetry : Command (Cell M P) α 80 :=
  ((FixedBlockRetry.retryLoop (CertifiedStarPhase.unitSymbol M) (CertifiedStarPhase.bitSymbol M)
    (StarCertification.width p) (CertifiedStarPhase.routine M p)).mapSymbols Sum.inl (outerDecode M P)).rename outerSlots

noncomputable def command : Command (Cell M P) α 80 :=
  (boot M P).seq ((pathRetry M p P).seq
    (ExpectedStarCalls.generatingCommand P (CertifiedStarPhase.projectPath M)))

attribute [irreducible] command

def initialMemory (random : ℕ) : Memory (Cell M P) α 80 := ⟨(), 0, random, [], fun _ => []⟩

def readyStore (n : ℕ) : Store M P :=
  Function.update (Function.update (fun _ => []) 13 (List.replicate n (unitSymbol M P)))
    22 (List.replicate n (unitSymbol M P))

def readyMemory (n random : ℕ) : Memory (Cell M P) α 80 := ⟨(), 0, random, [], readyStore M P n⟩

def outerStore (n : ℕ) : Local.Store (Outer M) 35 :=
  Function.update (Function.update (fun _ => []) 13 (List.replicate n (CertifiedStarPhase.unitSymbol M)))
    22 (List.replicate n (CertifiedStarPhase.unitSymbol M))

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
