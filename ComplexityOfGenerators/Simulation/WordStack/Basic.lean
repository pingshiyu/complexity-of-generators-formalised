import ComplexityOfGenerators.Simulation.TransducerBank.Execution

/-!
# Finite-control programs over a fixed bank of word stacks

Each instruction examines one stack head and the unary input index. It can
push or pop one symbol, emit one letter, move the index head, or read one
random bit. Thus no operation on an unbounded word is hidden in an instruction.
The following compiler represents every stack on one existing bank tape.
-/

namespace ComplexityOfGenerators.Simulation.WordStack

inductive Action (S : Type)
  | stay | push (symbol : S) | pop

def Action.apply {S : Type} : Action S → List S → List S
  | .stay, xs => xs
  | .push a, xs => a :: xs
  | .pop, xs => xs.tail

inductive Instruction (Q S O : Type)
  | accept | reject
  | random (no yes : Q)
  | step (next : Q) (action : Action S) (index : Move) (emit : Option O)

structure Program (Q S O : Type) (k : ℕ) where
  initial : Q
  select : Q → Fin k
  transition : Q → Option S → Option Unit → Instruction Q S O

@[ext] structure Configuration (Q S O : Type) (k : ℕ) where
  state : Q
  indexHead : ℕ
  randomHead : ℕ
  output : List O
  store : Fin k → List S

namespace Program

variable {Q S O : Type} {k : ℕ} (P : Program Q S O k)

def initialConfiguration : Configuration Q S O k := ⟨P.initial, 0, 0, [], fun _ => []⟩

def instruction (n : ℕ) (c : Configuration Q S O k) : Instruction Q S O :=
  P.transition c.state (c.store (P.select c.state)).head?
    (if c.indexHead < n then some () else none)

def advance (n : ℕ) (c : Configuration Q S O k) (next : Q) (action : Action S)
    (index : Move) (emit : Option O) : Configuration Q S O k :=
  {c with
    state := next
    indexHead := index.onInput n c.indexHead
    output := c.output ++ emit.toList
    store := Function.update c.store (P.select c.state)
      (action.apply (c.store (P.select c.state)))}

def choose (c : Configuration Q S O k) (next : Q) : Configuration Q S O k :=
  {c with state := next, randomHead := c.randomHead + 1}

inductive Executes (n : ℕ) (bits : BitString) :
    Configuration Q S O k → ℕ → Outcome O → Prop
  | accept (c) (table : P.instruction n c = .accept) : Executes n bits c 0 (.accepted c.output)
  | reject (c) (table : P.instruction n c = .reject) : Executes n bits c 0 .rejected
  | exhausted (c) (no yes : Q) (table : P.instruction n c = .random no yes)
      (absent : bits[c.randomHead]? = none) : Executes n bits c 0 .exhausted
  | random (c) (no yes : Q) (bit : Bool) (t result)
      (table : P.instruction n c = .random no yes) (lookup : bits[c.randomHead]? = some bit)
      (rest : Executes n bits (choose c (if bit then yes else no)) t result) :
      Executes n bits c (t + 1) result
  | step (c) (next action index emit) (t result)
      (table : P.instruction n c = .step next action index emit)
      (rest : Executes n bits (P.advance n c next action index emit) t result) :
      Executes n bits c (t + 1) result

end Program

/-- A stack occupies cells `1,…,length`; its head is at its final occupied
cell. Cell zero and all cells beyond its end are blank. -/
def tape {S : Type} (stack : List S) (i : ℤ) : Option S :=
  if 0 < i then stack.reverse[i.toNat - 1]? else none

@[simp] theorem tape_nil {S : Type} (i : ℤ) : tape ([] : List S) i = none := by
  simp [tape]

@[simp] theorem tape_origin {S : Type} (stack : List S) : tape stack 0 = none := by
  simp [tape]

@[simp] theorem tape_head {S : Type} (stack : List S) : tape stack stack.length = stack.head? := by
  cases stack with
  | nil => simp
  | cons a stack => simp [tape, List.reverse_cons]

@[simp] theorem tape_after {S : Type} (stack : List S) : tape stack (stack.length + 1) = none := by
  simp [tape]

theorem tape_push {S : Type} (stack : List S) (a : S) :
    tape (a :: stack) = Function.update (tape stack) (stack.length + 1) (some a) := by
  funext i
  by_cases equal : i = stack.length + 1
  · subst i
    simpa using tape_head (a :: stack)
  · rw [Function.update_of_ne equal]
    by_cases positive : 0 < i
    · have different : i.toNat - 1 ≠ stack.length := by
        have nat : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
        omega
      simp only [tape, positive, ↓reduceIte, List.reverse_cons]
      rw [List.getElem?_append]
      split_ifs with inside
      · rfl
      · have larger : stack.length < i.toNat - 1 := by simp only [List.length_reverse] at inside; omega
        have absent : stack.reverse[i.toNat - 1]? = none := List.getElem?_eq_none (by simp; omega)
        have beyond : 1 ≤ i.toNat - 1 - stack.reverse.length := by simp only [List.length_reverse]; omega
        rw [List.getElem?_eq_none (by simpa using beyond), absent]
    · simp [tape, positive]

theorem tape_pop {S : Type} (stack : List S) :
    tape stack.tail = Function.update (tape stack) (stack.length : ℤ) none := by
  cases stack with
  | nil => simp
  | cons a stack =>
    simp only [List.tail_cons, List.length_cons, Nat.cast_add, Nat.cast_one, tape_push,
      Function.update_idem]
    rw [← tape_after stack]
    exact (Function.update_eq_self _ _).symm

inductive Phase (Q S : Type) (k : ℕ)
  | ready (state : Q)
  | push (next : Q) (stack : Fin k) (symbol : S)
  deriving Fintype

namespace Program

variable {Q S O : Type} {k : ℕ} (P : Program Q S O k)

def bankSelect : Phase Q S k → Fin k
  | .ready q => P.select q
  | .push _ j _ => j

def bankTransition (q : Phase Q S k) (index : Option Unit) (origin : Bool) (cell : Option S) :
    TransducerBank.BankInstruction (Phase Q S k) (Option S) O :=
  match q with
  | .push next _ symbol => .step (.ready next) (some symbol) .stay .stay .stay .stay none
  | .ready q => match P.transition q cell index with
      | .accept => .accept
      | .reject => .reject
      | .random no yes => .readRandom (.ready no) (.ready yes)
      | .step next .stay index emit => .step (.ready next) cell .stay .stay .stay index emit
      | .step next (.push a) index emit => .step (.push next (P.select q) a) cell .right .stay .stay index emit
      | .step next .pop index emit =>
          .step (.ready next) none (if origin then .stay else .left) .stay .stay index emit

def bank : TransducerBank.TapeBank Unit Bool O (Phase Q S k) (Option S) k where
  initial := .ready P.initial
  blank := none
  select := P.bankSelect
  transition := fun q _ _ index origin cell => P.bankTransition q index origin cell

def encoded (_P : Program Q S O k) (c : Configuration Q S O k) :
    TransducerBank.BankConfiguration O (Phase Q S k) (Option S) k where
  state := .ready c.state
  inputHead := 0
  auxiliaryHead := 0
  indexHead := c.indexHead
  randomHead := c.randomHead
  output := c.output
  head := fun j => (c.store j).length
  tape := fun j => tape (c.store j)

@[simp] theorem encoded_initial : P.encoded P.initialConfiguration = P.bank.initialConfiguration := by
  simp [encoded, initialConfiguration, bank, TransducerBank.TapeBank.initialConfiguration,
    show (tape ([] : List S)) = fun _ => none from funext tape_nil]

end Program
end ComplexityOfGenerators.Simulation.WordStack
