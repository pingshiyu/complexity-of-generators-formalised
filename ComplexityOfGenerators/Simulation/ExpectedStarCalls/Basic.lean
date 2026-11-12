import ComplexityOfGenerators.Proofs.BoundedPhaseFamilies
import ComplexityOfGenerators.Simulation.FixedBlockRetry.LoopSuccess
import ComplexityOfGenerators.Simulation.StarPaths.Model
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding

/-! Sequential calls retry source phases inside one stack controller. The
physical output remains empty until the separate final emission command. -/
namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls

open WordStack

set_option backward.isDefEq.respectTransparency false

variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

abbrev InnerCell := BoundedMachinePhase.Cell P.machine
abbrev Cell := β ⊕ InnerCell P
abbrev Store := Local.Store (Cell (β := β) P) 80
abbrev Controller := WordStack.Routine (Cell (β := β) P) α 80

def innerSlots : Fin 35 ↪ Fin 80 where
  toFun i := ⟨35+i.val, by omega⟩
  inj' a b same := by
    apply Fin.ext
    have equality := congrArg (fun j : Fin 80 => j.val) same
    change 35+a.val = 35+b.val at equality
    omega

def innerDecode : Cell (β := β) P → InnerCell P := Sum.elim (fun _ => UnionGenerator.Symbol.unit) id

def outputLetter : Cell (β := β) P → Option α := Sum.elim (fun _ => none) (UnionGenerator.outputLetter P.machine P.machine)

def pathSymbol (encode : StarPaths.Symbol → β) (symbol : StarPaths.Symbol) : Cell (β := β) P := .inl (encode symbol)

def isUnit (decode : β → StarPaths.Symbol) : Cell (β := β) P → Bool
  | .inl symbol => decide (decode symbol = .unit)
  | .inr _ => false

def pathWord (encode : StarPaths.Symbol → β) (parts : List ℕ) : List (Cell (β := β) P) :=
  (StarPaths.payload parts).map (pathSymbol P encode)

def parseFactor (decode : β → StarPaths.Symbol) : Controller (β := β) P :=
  (Routine.clear 71).seq ((Routine.ofLocal (Local.pop 31)).seq
    (Routine.transferWhile 31 71 (by decide) (isUnit P decode) id))

def innerRegisters : List (Fin 80) := (List.finRange 35).map innerSlots

def setup : Controller (β := β) P :=
  (Routine.clearMany innerRegisters).seq
    ((Routine.assign 71 (innerSlots 13) 73 (by decide) (by decide) (by decide)
      (fun _ => Sum.inr (UnionGenerator.Symbol.unit : InnerCell P))).seq
      (Routine.assign 71 (innerSlots 22) 73 (by decide) (by decide) (by decide)
        (fun _ => Sum.inr (UnionGenerator.Symbol.unit : InnerCell P))))

def initialStore (j : ℕ) : Local.Store (InnerCell P) 35 :=
  Function.update (Function.update (fun _ => []) 13 (List.replicate j UnionGenerator.Symbol.unit))
    22 (List.replicate j UnionGenerator.Symbol.unit)

noncomputable def retry : Command (Cell (β := β) P) α 80 :=
  ((FixedBlockRetry.retryLoop UnionGenerator.Symbol.unit UnionGenerator.Symbol.bit P.seed
    (BoundedMachinePhase.phase P.machine P.seed P.clock)).mapSymbols Sum.inr (innerDecode P)).rename innerSlots

def saveWord : Controller (β := β) P := Routine.transfer (innerSlots 31) 70 (by decide) id

noncomputable def call (decode : β → StarPaths.Symbol) : Command (Cell (β := β) P) α 80 :=
  (parseFactor P decode).command.seq ((setup P).command.seq ((retry P).seq (saveWord P).command))

noncomputable def loop (decode : β → StarPaths.Symbol) : Command (Cell (β := β) P) α 80 :=
  .loop 31 (fun observation => observation.1.isSome) (call P decode)

/-- Source words are buffered in reverse order, without physical emissions. -/
noncomputable def command (decode : β → StarPaths.Symbol) : Command (Cell (β := β) P) α 80 :=
  (Routine.clear (O := α) 70).command.seq (loop P decode)

def emit : Command (Cell (β := β) P) α 80 :=
  (Routine.clear (O := α) 74).command.seq
    ((Routine.transfer (O := α) 70 74 (by decide) id).command.seq (Command.emitWord 74 (outputLetter P)))

end ComplexityOfGenerators.Simulation.ExpectedStarCalls
