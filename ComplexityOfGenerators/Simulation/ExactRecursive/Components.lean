import ComplexityOfGenerators.Simulation.WordStack.SourceCall
import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
import ComplexityOfGenerators.Simulation.WordStack.Blocks
import ComplexityOfGenerators.Simulation.WordStack.WordCounter
import ComplexityOfGenerators.Simulation.WordStack.Shortlex
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

/-! Finite components of the exact-recursive generator. The source interpreters
share a register bank and use disjoint tags in one finite work alphabet. -/

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

inductive Symbol (α : Type) (B : Machine Unit Bool α) (V : Machine α α α)
  | letter (a : α)
  | bit (b : Bool)
  | unit
  | base (cell : Source.Symbol B)
  | inverse (cell : Source.Symbol V)
  deriving Fintype

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

abbrev Cell := Symbol α B V
abbrev Store := Local.Store (Cell B V) 35
abbrev Controller := WordStack.Routine (Cell B V) α 35

def sourceSlots : Source.Layout 35 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j eq; exact Fin.ext (congrArg (fun i : Fin 35 => i.val) eq)

@[simp] theorem sourceSlots_apply (i : Fin 17) : sourceSlots i = ⟨i.val, by omega⟩ := rfl

def counterSlots (value : Fin 35) (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21) :
    CounterRoutine.Layout 35 where
  toFun
    | 0 => 13
    | 1 => value
    | 2 => 19
    | 3 => 20
    | 4 => 21
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all [ne_comm]

@[simp] theorem counterSlots_apply (value : Fin 35)
    (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21) (i : Fin 5) :
    counterSlots value different i = match i with
      | 0 => 13 | 1 => value | 2 => 19 | 3 => 20 | 4 => 21 := rfl

def counter (value : Fin 35) (different : value ≠ 13 ∧ value ≠ 19 ∧ value ≠ 20 ∧ value ≠ 21)
    (p : PolynomialBound) : Controller B V := CounterRoutine.routine (counterSlots value different) p .unit

def baseDecode : Cell B V → Source.Symbol B
  | .base cell => cell
  | _ => .unit

def inverseDecode : Cell B V → Source.Symbol V
  | .inverse cell => cell
  | _ => .unit

def baseBit : Cell B V → Cell B V
  | .bit b => .base (.bit b)
  | _ => .base (.bit false)

def inverseBit : Cell B V → Cell B V
  | .bit b => .inverse (.bit b)
  | _ => .inverse (.bit false)

def inverseInput : Cell B V → Cell B V
  | .letter a => .inverse (.input a)
  | _ => .inverse .unit

def inverseAuxiliary : Cell B V → Cell B V
  | .letter a => .inverse (.auxiliary a)
  | _ => .inverse .unit

def baseOutput : Cell B V → Cell B V
  | .base (.output a) => .letter a
  | _ => .unit

def inverseOutput : Cell B V → Cell B V
  | .inverse (.output a) => .letter a
  | _ => .unit

noncomputable def sourceTrial {I A : Type} (M : Machine I A α)
    (encode : Source.Symbol M → Cell B V) (decode : Cell B V → Source.Symbol M)
    (inputMap auxiliaryMap bitMap : Cell B V → Cell B V)
    (seed time : PolynomialBound) : Controller B V :=
  (counter B V 18 (by decide) seed).seq
  ((Blocks.routine 18 17 14 (by decide) (by decide)).seq
  ((counter B V 16 (by decide) time).seq
  ((WordStack.Routine.ofLocal (Local.push 16 .unit)).seq
    (Source.call M sourceSlots encode decode inputMap auxiliaryMap bitMap))))

noncomputable def baseTrial (seed time : PolynomialBound) : Controller B V :=
  sourceTrial B V B Symbol.base (baseDecode B V) (fun _ => .base .unit) (fun _ => .base .unit)
    (baseBit B V) seed time

noncomputable def inverseTrial (seed time : PolynomialBound) : Controller B V :=
  sourceTrial B V V Symbol.inverse (inverseDecode B V) (inverseInput B V) (inverseAuxiliary B V)
    (inverseBit B V) seed time

def flag (reg : Fin 35) (value : Bool) : Controller B V :=
  (WordStack.Routine.clear reg).seq (if value then WordStack.Routine.ofLocal (Local.push reg .unit) else WordStack.Routine.skip)

/-- A coin is read from the previously collected random block. -/
def coin (no yes : Controller B V) : Controller B V :=
  WordStack.Routine.branch 17 fun head =>
    (WordStack.Routine.ofLocal (Local.pop 17)).seq (match head with | some (.bit true) => yes | _ => no)

def takeOutput (destination : Fin 35) (different : (10 : Fin 35) ≠ destination)
    (map : Cell B V → Cell B V) : Controller B V :=
  (WordStack.Routine.clear destination).seq (WordStack.Routine.transfer 10 destination different map)

/-- Register 26 locks the chosen result; 27 records whether any positive
inverse trial has succeeded. -/
def offer (coin : Bool) : Controller B V :=
  WordStack.Routine.branch 26 fun locked => if locked.isSome then WordStack.Routine.skip else
    WordStack.Routine.branch 12 fun label => if label.isNone then WordStack.Routine.skip else
      WordStack.Routine.branch 0 fun status => match status with
        | some (.inverse (.state .accepted)) =>
          (takeOutput B V 25 (by decide) (inverseOutput B V)).seq
            ((flag B V 27 true).seq (if coin then flag B V 26 true else WordStack.Routine.skip))
        | _ => WordStack.Routine.skip

noncomputable def nextLetter : Cell B V → Option (Cell B V)
  | .letter a => (CyclicGenerator.nextLetter a).map Symbol.letter
  | _ => none

noncomputable def increment (first : α) : Controller B V :=
  WordCounter.routine 12 24 (by decide) (.letter first) (nextLetter B V)

noncomputable def searchStep (first : α) (seed time : PolynomialBound) : Controller B V :=
  (inverseTrial B V seed time).seq
    ((coin B V (offer B V false) (offer B V true)).seq (increment B V first))

end ComplexityOfGenerators.Simulation.ExactRecursive
