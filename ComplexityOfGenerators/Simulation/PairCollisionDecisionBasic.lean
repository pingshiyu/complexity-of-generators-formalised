import ComplexityOfGenerators.Simulation.PairCollisionExpandTwo
import ComplexityOfGenerators.Simulation.PairCollisionEncoder
import ComplexityOfGenerators.Simulation.WordStack.SourceCall
import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
import ComplexityOfGenerators.Simulation.WordStack.BooleanReturn
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Proofs.PolynomialCollisionDecision

namespace ComplexityOfGenerators.Simulation.PairCollisionDecision
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Cell (M : Machine Bool Bool Unit)
  | source (symbol : Source.Symbol M)
  | pair (symbol : PairSymbol)
  | unit
  deriving Fintype

variable (M : Machine Bool Bool Unit)
abbrev Store := Local.Store (Cell M) 32
abbrev Controller := WordStack.Routine (Cell M) Unit 32

abbrev sourceSlots : Source.Layout 32 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro i j equal;exact Fin.ext (congrArg (fun i : Fin 32=>i.val) equal)

@[simp] theorem sourceSlots_apply (i : Fin 17) : sourceSlots i=⟨i.val,by omega⟩ := rfl

def counterSlots : CounterRoutine.Layout 32 where
  toFun | 0=>20 | 1=>16 | 2=>23 | 3=>24 | 4=>25
  inj' := by intro i j equal;fin_cases i <;>fin_cases j <;>simp_all

@[simp] theorem counterSlots_apply (i : Fin 5) :
    counterSlots i=match i with | 0=>20 | 1=>16 | 2=>23 | 3=>24 | 4=>25 := rfl

def sourceDecode : Cell M→Source.Symbol M
  | .source symbol=>symbol
  | _=>.unit

def first : Cell M→Cell M
  | .pair symbol=>.source (.input (PairCollisionEncoder.first symbol))
  | _=>.unit

def second : Cell M→Cell M
  | .pair symbol=>.source (.input (PairCollisionEncoder.second symbol))
  | _=>.unit

def sourceClock (p : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (p.asPolynomial.comp (2*Polynomial.X)+1)

theorem sourceClock_lower (p : PolynomialBound) (n : ℕ) : p (2*n)+1≤sourceClock p n := by
  have bound := PolynomialBound.eval_le_ofPolynomial (p.asPolynomial.comp (2*Polynomial.X)+1) n
  simpa [sourceClock,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    PolynomialBound.asPolynomial_eval] using bound

def counter (p : PolynomialBound) : Controller M := CounterRoutine.routine counterSlots (sourceClock p) .unit

def expand : Controller M := PairCollisionExpandTwo.routine 20 11 (by decide) (first M) (second M)

def prepare (p : PolynomialBound) : Controller M := (counter M p).seq (expand M)

def call : Controller M := Source.call M sourceSlots Cell.source (sourceDecode M) id id id

def routine (p : PolynomialBound) : Controller M := (prepare M p).seq (call M)

def loaded (word : List PairSymbol) : Memory (Cell M) Unit 32 :=
  ⟨(),0,0,[],Function.update (fun _=>[]) 20 (word.reverse.map Cell.pair)⟩

def prepared (p : PolynomialBound) (word : List PairSymbol) : Store M :=
  (prepare M p).eval (loaded M word).store

theorem blocks_input (word : List PairSymbol) :
    PairCollisionExpandTwo.blocks (first M) (second M) (word.map Cell.pair)=
      (binaryPairWord word).map (fun b=>Cell.source (.input b)) := by
  induction word with
  | nil=>rfl
  | cons symbol tail ih=>
      cases symbol <;>
        simp [PairCollisionExpandTwo.blocks,binaryPairWord,pairSymbolBits,first,second,
          PairCollisionEncoder.first,PairCollisionEncoder.second] at ih ⊢ <;>exact ih

theorem prepared_eq (p : PolynomialBound) (word : List PairSymbol) :
    prepared M p word=Function.update
      (Function.update (Function.update (fun _ : Fin 32=>([] : List (Cell M))) 23 (List.replicate (word.length+1) .unit))
        16 (List.replicate (sourceClock p word.length) .unit))
      11 ((binaryPairWord word).map (fun b=>Cell.source (.input b))) := by
  funext j
  by_cases h11 : j=11 <;>by_cases h16 : j=16 <;>by_cases h23 : j=23 <;>
    simp_all [prepared,prepare,counter,expand,CounterRoutine.routine_eval,
      PairCollisionExpandTwo.routine,loaded,Routine.seq,Function.update_apply,
      List.map_reverse,blocks_input]

theorem prepared_input (p : PolynomialBound) (word : List PairSymbol) :
    (prepared M p word 11).map id=(binaryPairWord word).map (fun b=>Cell.source (.input b)) := by
  simp [prepared_eq]

theorem prepared_auxiliary (p : PolynomialBound) (word : List PairSymbol) : prepared M p word 12=[] := by
  simp [prepared_eq]

theorem prepared_index (p : PolynomialBound) (word : List PairSymbol) : (prepared M p word 13).length=0 := by
  simp [prepared_eq]

theorem prepared_bits (p : PolynomialBound) (word : List PairSymbol) : prepared M p word 14=[] := by
  simp [prepared_eq]

theorem prepared_clock (p : PolynomialBound) (word : List PairSymbol) :
    (prepared M p word 16).length=sourceClock p word.length := by simp [prepared_eq]

end
end ComplexityOfGenerators.Simulation.PairCollisionDecision
