import ComplexityOfGenerators.Simulation.TapeBank

/-!
# Finite tape banks with random input and output

The decision-only tape-bank compiler is extended here to the interfaces needed
by sampler/recoverer composition. An instruction still accesses just one work
cell. Input, auxiliary and unary-index heads move by at most one; random bits
are consumed one at a time, and output symbols are appended one at a time.
The index-symbol interface is `Option Unit`, matching the native machine.
-/

namespace ComplexityOfGenerators.Simulation.TransducerBank

inductive BankInstruction (Q S O : Type)
  | accept | reject
  | readRandom (no yes : Q)
  | step (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O)

structure TapeBank (I A O Q S : Type) (k : ℕ) where
  initial : Q
  blank : S
  select : Q → Fin k
  transition : Q → Option I → Option A → Option Unit → Bool → S → BankInstruction Q S O

@[ext] structure BankConfiguration (O Q S : Type) (k : ℕ) where
  state : Q
  inputHead : ℕ
  auxiliaryHead : ℕ
  indexHead : ℕ
  randomHead : ℕ
  output : List O
  head : Fin k → ℤ
  tape : Fin k → ℤ → S

namespace TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

def initialConfiguration : BankConfiguration O Q S k :=
  ⟨B.initial, 0, 0, 0, 0, [], fun _ => 0, fun _ _ => B.blank⟩

def instruction (data : InputData I A) (c : BankConfiguration O Q S k) : BankInstruction Q S O :=
  B.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none)
    (decide (c.head (B.select c.state) = 0)) (c.tape (B.select c.state) (c.head (B.select c.state)))

def advance (data : InputData I A) (c : BankConfiguration O Q S k)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O) : BankConfiguration O Q S k :=
  ⟨next, input.onInput data.input.length c.inputHead, auxiliary.onInput data.auxiliary.length c.auxiliaryHead,
    index.onInput data.index c.indexHead, c.randomHead, c.output ++ emit.toList,
    Function.update c.head (B.select c.state) (work.onInt (c.head (B.select c.state))),
    Function.update c.tape (B.select c.state)
      (Function.update (c.tape (B.select c.state)) (c.head (B.select c.state)) write)⟩

def choose (c : BankConfiguration O Q S k) (next : Q) : BankConfiguration O Q S k :=
  {c with state := next, randomHead := c.randomHead + 1}

inductive Executes (data : InputData I A) (bits : BitString) :
    BankConfiguration O Q S k → ℕ → Outcome O → Prop
  | accept (c) (table : B.instruction data c = .accept) : Executes data bits c 0 (.accepted c.output)
  | reject (c) (table : B.instruction data c = .reject) : Executes data bits c 0 .rejected
  | exhausted (c) (no yes : Q) (table : B.instruction data c = .readRandom no yes)
      (absent : bits[c.randomHead]? = none) : Executes data bits c 0 .exhausted
  | random (c) (no yes : Q) (bit : Bool) (t result)
      (table : B.instruction data c = .readRandom no yes) (lookup : bits[c.randomHead]? = some bit)
      (rest : Executes data bits (choose c (if bit then yes else no)) t result) :
      Executes data bits c (t + 1) result
  | step (c) (next write work input auxiliary index emit) (t result)
      (table : B.instruction data c = .step next write work input auxiliary index emit)
      (rest : Executes data bits (B.advance data c next write work input auxiliary index emit) t result) :
      Executes data bits c (t + 1) result

structure Bounded (_ : TapeBank I A O Q S k) (data : InputData I A) (r : ℕ)
    (c : BankConfiguration O Q S k) : Prop where
  input : c.inputHead ≤ data.input.length
  auxiliary : c.auxiliaryHead ≤ data.auxiliary.length
  index : c.indexHead ≤ data.index
  head : ∀ j, (c.head j).natAbs ≤ r

theorem initial_bounded (data : InputData I A) : B.Bounded data 0 B.initialConfiguration := by
  constructor <;> simp [initialConfiguration]

theorem advance_bounded (data : InputData I A) (r : ℕ) (c : BankConfiguration O Q S k)
    (next write work input auxiliary index emit) (h : B.Bounded data r c) :
    B.Bounded data (r + 1) (B.advance data c next write work input auxiliary index emit) := by
  refine ⟨input.onInput_le _ _ h.input, auxiliary.onInput_le _ _ h.auxiliary,
    index.onInput_le _ _ h.index, ?_⟩
  intro j
  by_cases same : j = B.select c.state
  · subst j
    simp only [advance, Function.update_self]
    have bound := h.head (B.select c.state)
    cases work with
    | stay => exact bound.trans (Nat.le_succ r)
    | left => exact (Int.natAbs_sub_le _ 1).trans (by simpa using Nat.add_le_add_right bound 1)
    | right => exact (Int.natAbs_add_le _ 1).trans (by simpa using Nat.add_le_add_right bound 1)
  · simpa [advance, Function.update_of_ne same] using (h.head j).trans (Nat.le_succ r)

theorem choose_bounded (data : InputData I A) (r : ℕ) (c : BankConfiguration O Q S k)
    (next : Q) (h : B.Bounded data r c) : B.Bounded data (r + 1) (choose c next) :=
  ⟨h.input, h.auxiliary, h.index, fun j => (h.head j).trans (Nat.le_succ r)⟩

end TapeBank
end ComplexityOfGenerators.Simulation.TransducerBank
