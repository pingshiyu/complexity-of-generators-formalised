import ComplexityOfGenerators.Simulation.WordStack.BoundedInput
import ComplexityOfGenerators.Simulation.WordStack.LengthTest
import ComplexityOfGenerators.Simulation.WordStack.Output
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native

/-! Bounded source execution followed by native length and width checks. -/
namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

inductive Symbol (M : Machine α α α) (W : Machine α Unit Unit)
  | unit
  | bit (b : Bool)
  | letter (a : α)
  | inverse (cell : Source.Symbol M)
  | width (cell : Source.Symbol W)
  deriving Fintype

variable (M : Machine α α α) (W : Machine α Unit Unit)
abbrev Cell := Symbol M W
abbrev Store := Local.Store (Cell M W) 35
abbrev Controller := WordStack.Routine (Cell M W) α 35

def letters (word : List α) : List (Cell M W) := word.map Symbol.letter

def inverseDecode : Cell M W→Source.Symbol M
  | .inverse cell => cell
  | _ => .unit

def widthDecode : Cell M W→Source.Symbol W
  | .width cell => cell
  | _ => .unit

def inverseInput : Cell M W→Cell M W
  | .letter a => .inverse (.input a)
  | _ => .inverse .unit

def inverseAuxiliary : Cell M W→Cell M W
  | .letter a => .inverse (.auxiliary a)
  | _ => .inverse .unit

def inverseBit : Cell M W→Cell M W
  | .bit b => .inverse (.bit b)
  | _ => .inverse (.bit false)

def inverseOutput : Cell M W→Cell M W
  | .inverse (.output a) => .letter a
  | _ => .unit

def widthInput : Cell M W→Cell M W
  | .letter a => .width (.input a)
  | _ => .width .unit

def counter (reg : Fin 35) (different : reg≠13 ∧ reg≠19 ∧ reg≠20 ∧ reg≠21)
    (p : PolynomialBound) : Controller M W :=
  BoundedSource.counter Symbol.unit Symbol.bit reg different p

def flag (reg : Fin 35) (yes : Bool) : Controller M W :=
  (WordStack.Routine.clear reg).seq (if yes then WordStack.Routine.ofLocal (Local.push reg Symbol.unit) else WordStack.Routine.skip)

theorem flag_eval (reg : Fin 35) (yes : Bool) (s : Store M W) :
    (flag M W reg yes).eval s=Function.update s reg (if yes then [Symbol.unit] else []) := by
  cases yes <;> simp [flag,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.ofLocal,WordStack.Routine.skip,Local.eval_push]

/-- A length-at-most test retaining the tested word and its comparison word. -/
def atMost : Controller M W :=
  (WordStack.Routine.assign 13 30 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit)).seq
  ((WordStack.Routine.assign 25 29 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.clear 31).seq
  ((DrainPair.routine 30 29 31 (by decide) (by decide)).seq
  (WordStack.Routine.branch 29 (fun head=>flag M W 27 head.isNone)))))

def equalitySlots : LengthTest.Layout 35 where
  toFun | 0=>10 | 1=>23 | 2=>28 | 3=>29 | 4=>30 | 5=>31
  inj' := by intro i j eq;fin_cases i <;> fin_cases j <;> simp_all

/-- The width source runs on the candidate as ordinary input and index zero. -/
def widthSetup (q : PolynomialBound) : Controller M W :=
  (WordStack.Routine.assign 25 11 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.clear 12).seq
  ((counter M W 16 (by decide) q).seq
  ((WordStack.Routine.ofLocal (Local.push 16 Symbol.unit)).seq
  ((WordStack.Routine.clear 13).seq (WordStack.Routine.clear 14)))))

noncomputable def widthCall : Controller M W :=
  Source.call W BoundedSource.sourceSlots Symbol.width (widthDecode M W) (widthInput M W)
    (fun _=>.width .unit) (fun _=>.width (.bit false))

noncomputable def widthCheck (q : PolynomialBound) : Controller M W :=
  (widthSetup M W q).seq
  ((widthCall M W).seq (LengthTest.routine equalitySlots Symbol.unit))

noncomputable def firstCall (seed time : PolynomialBound) : Controller M W :=
  BoundedSource.sourceTrial Symbol.unit Symbol.bit M Symbol.inverse (inverseDecode M W)
    (inverseInput M W) (inverseAuxiliary M W) (inverseBit M W) seed time

def sourceFlag : Controller M W :=
  WordStack.Routine.branch 0 fun (head : Option (Cell M W))=>match head with
    | some (.inverse (.state .accepted)) => flag M W 26 true
    | _ => flag M W 26 false

def capture : Controller M W :=
  (sourceFlag M W).seq
  ((WordStack.Routine.assign 12 23 33 (by decide) (by decide) (by decide) (fun _=>Symbol.unit)).seq
    (WordStack.Routine.transfer 10 25 (by decide) (inverseOutput M W)))

noncomputable def checks (widthTime : PolynomialBound) : Controller M W :=
  (atMost M W).seq
  (WordStack.Routine.branch 26 fun accepted=>if accepted.isSome then
    WordStack.Routine.branch 27 fun short=>if short.isSome then widthCheck M W widthTime else flag M W 28 false
   else flag M W 28 false)

noncomputable def body (seed time widthTime : PolynomialBound) : Controller M W :=
  (firstCall M W seed time).seq ((capture M W).seq (checks M W widthTime))

def decodeOutput : Cell M W→Option α
  | .letter a => some a
  | _ => none

def finish : Command (Cell M W) α 35 :=
  .branch 26 fun accepted=>if accepted.1.isSome then
    .branch 27 fun short=>if short.1.isSome then
      .branch 28 fun equalWidth=>if equalWidth.1.isSome then Command.emitWord 25 (decodeOutput M W) else .drain
    else .drain
  else .drain

def slots : Fin 35↪Fin 37 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j eq;exact Fin.ext (congrArg (fun i : Fin 37 => i.val) eq)

@[simp] theorem slots_val (i : Fin 35) : (slots i).val=i.val := rfl

def loadWords : WordStack.Routine (Cell M W) α 37 :=
  (WordStack.Routine.transfer 35 11 (by decide) id).seq (WordStack.Routine.transfer 36 12 (by decide) id)

noncomputable def command (seed time widthTime : PolynomialBound) : Command (Cell M W) α 37 :=
  ((BoundedSource.prepareCommand (O := α) Symbol.unit Symbol.bit seed).rename slots).seq
  ((loadWords M W).command.seq
  (((body M W seed time widthTime).command.rename slots).seq ((finish M W).rename slots)))

noncomputable def machine (seed time widthTime : PolynomialBound) : Machine α α α :=
  let code := command M W seed time widthTime
  InputBank.machine (code.program 0) 35 36 Symbol.letter Symbol.letter

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
