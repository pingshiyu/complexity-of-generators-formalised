import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.EmptyPhase
import ComplexityOfGenerators.Simulation.WordStack.OutputErasure

/-! A bounded controller selects a certified positive composition, then emits
one call event per factor. The factor size is exported on stack 71; the native
hook consumes the event and runs the original source directly. -/
namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

abbrev Cell := ExpectedStarGenerator.Cell M (emptyPhase (α := α))
abbrev Store := Local.Store (Cell M) 80
abbrev Controller := WordStack.Routine (Cell M) Unit 80

def unitSymbol : Cell M := ExpectedStarGenerator.unitSymbol M emptyPhase

def pathWord (parts : List ℕ) : List (Cell M) :=
  ExpectedStarCalls.pathWord emptyPhase (CertifiedStarPhase.encodePath M) parts

def boot : Command (Cell M) Unit 80 :=
  (ExpectedStarGenerator.boot M emptyPhase).mapOutput (fun _=>())

noncomputable def pathRetry : Command (Cell M) Unit 80 :=
  (ExpectedStarGenerator.pathRetry M p emptyPhase).mapOutput (fun _=>())

/-- The complete certification prefix physically emits no call events,
including when a finite tape exhausts during a retry. -/
noncomputable def prelude : Command (Cell M) Unit 80 :=
  ((boot M).seq (pathRetry M p)).filterMapOutput (fun _=>none : Unit→Option Unit)

/-- The stored path uses `cut` followed by one unit per factor position. -/
def parseFactor : Controller M :=
  (Routine.clear 71).seq ((Routine.ofLocal (Local.pop 31)).seq
    (Routine.transferWhile 31 71 (by decide)
      (ExpectedStarCalls.isUnit emptyPhase (CertifiedStarPhase.projectPath M)) id))

/-- Register rows start at one. Exporting `j-1` symbols and treating the common
origin row as live yields exactly the unary parameter cells `0,...,j-1`. -/
def prepareFactor : Controller M :=
  (parseFactor M).seq (Routine.ofLocal (Local.pop 71))

/-- The selected event register stays empty, so the compiled native event is
emitted at physical work position zero without moving that head. -/
def event : Command (Cell M) Unit 80 := .act 0 .stay .stay (some ())

def call : Command (Cell M) Unit 80 := (prepareFactor M).command.seq (event M)

def loop : Command (Cell M) Unit 80 := .loop 31 (fun observation=>observation.1.isSome) (call M)

def events : Command (Cell M) Unit 80 := (Routine.clear (O := Unit) 0).command.seq (loop M)

noncomputable def command : Command (Cell M) Unit 80 :=
  (prelude M p).seq (events M)


def initialMemory (random : ℕ) : Memory (Cell M) Unit 80 := ⟨(),0,random,[],fun _=>[]⟩

def readyMemory (n random : ℕ) : Memory (Cell M) Unit 80 :=
  (ExpectedStarGenerator.readyMemory M emptyPhase n random).mapOutput (fun _=>())

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
