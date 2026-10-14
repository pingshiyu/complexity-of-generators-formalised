import ComplexityOfGenerators.Simulation.TransducerBank.Execution

/-!
# The finite program composing sampler and recoverer

Four work tapes hold sampler work, the unary index, the sampled certificate,
and recoverer work. The stored index uses Boolean occupancy flags, decoded to
`Option Unit` when calling either source machine; certificates remain binary.
Index and certificate heads are rewound by scanning their
origin markers before recovery. Sampler output is written one bit at a time;
recoverer output is emitted one symbol at a time. The physical random cursor
is shared. Explicit sampler failure enters a random-tape drain.
-/

namespace ComplexityOfGenerators.Simulation

@[ext] structure CompositionCell (samplerSymbols recovererSymbols : ℕ) where
  sampler : Option (Fin samplerSymbols) := none
  recoverer : Option (Fin recovererSymbols) := none
  certificate : Option Bool := none
  index : Bool := false
  deriving DecidableEq, Fintype

noncomputable section
local instance compositionMoveFintype : Fintype Move := Fintype.ofFinite _

inductive CompositionPhase (samplerStates recovererStates : ℕ)
  | load | rewindLoad
  | sample (q : Fin samplerStates)
  | sampleWork (q : Fin samplerStates) (index : Bool)
  | sampleIndex (q : Fin samplerStates) (index : Move) (emit : Option Bool)
  | sampleEmit (q : Fin samplerStates) (emit : Option Bool)
  | resetIndex | resetCertificate
  | recover (q : Fin recovererStates)
  | recoverAux (q : Fin recovererStates) (index : Bool)
  | recoverWork (q : Fin recovererStates) (index : Bool) (certificate : Option Bool)
  | recoverIndex (q : Fin recovererStates) (index auxiliary : Move)
  | recoverAuxMove (q : Fin recovererStates) (auxiliary : Move)
  | drain
  deriving Fintype

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

abbrev CompositionState := CompositionPhase S.states R.states
abbrev CompositionSymbol := CompositionCell S.symbols R.symbols

def compositionSelect : CompositionState S R → Fin 4
  | .load | .rewindLoad | .sample _ | .sampleIndex _ _ _ | .resetIndex | .recover _ | .recoverIndex _ _ _ => 1
  | .sampleEmit _ _ | .resetCertificate | .recoverAux _ _ | .recoverAuxMove _ _ => 2
  | .sampleWork _ _ | .drain => 0
  | .recoverWork _ _ _ => 3

def clampedReadMove (origin live : Bool) : Move → Move
  | .left => if origin then .stay else .left
  | .stay => .stay
  | .right => if live then .right else .stay

def compositionTransition (q : CompositionState S R) (index : Option Unit) (origin : Bool)
    (cell : CompositionSymbol S R) : TransducerBank.BankInstruction (CompositionState S R) (CompositionSymbol S R) α :=
  let step := fun q cell move emit => TransducerBank.BankInstruction.step q cell move .stay .stay .stay emit
  match q with
  | .load => match index with
      | some _ => .step .load {cell with index := true} .right .stay .stay .right none
      | none => step .rewindLoad cell .stay none
  | .rewindLoad => if origin then step (.sample S.initial) cell .stay none else step .rewindLoad cell .left none
  | .sample q => step (.sampleWork q cell.index) cell .stay none
  | .sampleWork q index => match S.transition q none none (if index then some () else none) cell.sampler with
      | .accept => step .resetIndex cell .stay none
      | .reject => .readRandom .drain .drain
      | .readRandom no yes => .readRandom (.sample no) (.sample yes)
      | .step next write work _ _ index emit =>
          step (.sampleIndex next index emit)
            {cell with sampler := match write with | none => cell.sampler | some a => some a} work none
  | .sampleIndex q index emit => step (.sampleEmit q emit) cell (clampedReadMove origin cell.index index) none
  | .sampleEmit q emit => match emit with
      | none => step (.sample q) cell .stay none
      | some bit => step (.sample q) {cell with certificate := some bit} .right none
  | .resetIndex => if origin then step .resetCertificate cell .stay none else step .resetIndex cell .left none
  | .resetCertificate => if origin then step (.recover R.initial) cell .stay none else step .resetCertificate cell .left none
  | .recover q => step (.recoverAux q cell.index) cell .stay none
  | .recoverAux q index => step (.recoverWork q index cell.certificate) cell .stay none
  | .recoverWork q index certificate => match R.transition q none certificate (if index then some () else none) cell.recoverer with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes => .readRandom (.recover no) (.recover yes)
      | .step next write work _ auxiliary index emit =>
          step (.recoverIndex next index auxiliary)
            {cell with recoverer := match write with | none => cell.recoverer | some a => some a} work emit
  | .recoverIndex q index auxiliary => step (.recoverAuxMove q auxiliary) cell (clampedReadMove origin cell.index index) none
  | .recoverAuxMove q auxiliary => step (.recover q) cell (clampedReadMove origin cell.certificate.isSome auxiliary) none
  | .drain => .readRandom .drain .drain

def samplerCompositionBank : TransducerBank.TapeBank Unit Bool α (CompositionState S R) (CompositionSymbol S R) 4 where
  initial := .load
  blank := {}
  select := compositionSelect S R
  transition := fun q _ _ index origin cell => compositionTransition S R q index origin cell

end
end ComplexityOfGenerators.Simulation
