import ComplexityOfGenerators.Simulation.StackSpace.Memory
import ComplexityOfGenerators.Proofs.NativeSpaceCompilation

/-!
# A finite-control compiler for Mathlib's stack instructions

The finite control contains only program subexpressions and the source's
finite local variables. Stack contents are on work tapes. Each push, pop or
peek takes at most two bank steps; no list operation is hidden in a transition.
-/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing

noncomputable section

variable {S Q V : Type} {k : ℕ} [Fintype Q]

abbrev Stmt (S Q V : Type) (k : ℕ) := TM2.Stmt (fun _ : Fin (k + 1) => S) Q V

def statements (P : Q → Stmt S Q V k) : Finset (Stmt S Q V k) :=
  by classical exact Finset.univ.biUnion fun q => TM2.stmts₁ (P q)

abbrev Node (P : Q → Stmt S Q V k) := ↥(statements P)

theorem statement_mem (P : Q → Stmt S Q V k) (q : Q) : P q ∈ statements P := by
  classical
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, TM2.stmts₁_self⟩

theorem substatement_mem (P : Q → Stmt S Q V k) {a b : Stmt S Q V k}
    (ha : a ∈ statements P) (hb : b ∈ TM2.stmts₁ a) : b ∈ statements P := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, TM2.stmts₁_trans hq hb⟩

def node (P : Q → Stmt S Q V k) (q : Q) : Node P := ⟨P q, statement_mem P q⟩

def child (P : Q → Stmt S Q V k) (a : Node P) (b : Stmt S Q V k)
    (h : b ∈ TM2.stmts₁ a.val) : Node P := ⟨b, substatement_mem P a.property h⟩

inductive Control (N V : Type)
  | load
  | exec (code : N) (var : V)
  | read (code : N) (var : V)
  | halt (var : V)
  deriving Fintype

abbrev State (P : Q → Stmt S Q V k) := Control (Node P) V
abbrev Config (P : Q → Stmt S Q V k) := TransducerBank.BankConfiguration Unit (State P) (Option S) (k + 1)

def selected (P : Q → Stmt S Q V k) : State P → Fin (k + 1)
  | .exec a _ | .read a _ => match a.val with
    | .push j _ _ | .pop j _ _ | .peek j _ _ => j
    | _ => 0
  | _ => 0

def transition (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
    (state : State P) (input : Option S) (origin : Bool) (cell : Option S) :
    TransducerBank.BankInstruction (State P) (Option S) Unit := by
  classical
  let step : State P → Option S → Move → TransducerBank.BankInstruction (State P) (Option S) Unit := fun next write move => TransducerBank.BankInstruction.step next write move .stay .stay .stay none
  exact match state with
  | .load => match input with
      | some s => .step .load (some s) .right .right .stay .stay none
      | none => step (.exec (node P entry) initial) cell .stay
  | .halt v => if answer v then .accept else .reject
  | .exec ⟨a, ha⟩ v => match a with
      | .push j f b => step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v)
          (some (f v)) .right
      | .peek j f b =>
          if origin then step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v none)) cell .stay
          else step (.read ⟨.peek j f b, ha⟩ v) cell .left
      | .pop j f b =>
          if origin then step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v none)) cell .stay
          else step (.read ⟨.pop j f b, ha⟩ v) cell .left
      | .load f b => step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v)) cell .stay
      | .branch f b c =>
          if f v then step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v) cell .stay
          else step (.exec ⟨c, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v) cell .stay
      | .goto f => step (.exec (node P (f v)) v) cell .stay
      | .halt => step (.halt v) cell .stay
  | .read ⟨a, ha⟩ v => match a with
      | .pop j f b => step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v cell)) none .stay
      | .peek j f b => step (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v cell)) cell .right
      | _ => .reject

def bank (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool) :
    TransducerBank.TapeBank S Bool Unit (State P) (Option S) (k + 1) where
  initial := .load
  blank := none
  select := selected P
  transition := fun state input _ _ origin cell => transition P entry initial answer state input origin cell

theorem bank_deterministic (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool) :
    (bank P entry initial answer).Deterministic := by
  intro state input auxiliary index origin cell
  cases state with
  | load => cases input <;> trivial
  | halt v => simp only [bank, transition]; split_ifs <;> trivial
  | exec a v =>
      rcases a with ⟨a, ha⟩
      cases a <;> simp only [bank, transition] <;> first | trivial | (split_ifs <;> trivial)
  | read a v => rcases a with ⟨a, ha⟩; cases a <;> trivial

/-- The head is just beyond the top; all other interfaces are inert after loading. -/
def configuration (P : Q → Stmt S Q V k) (inputLength : ℕ) (state : State P)
    (stk : Fin (k + 1) → List S) : Config P where
  state := state
  inputHead := inputLength
  auxiliaryHead := 0
  indexHead := 0
  randomHead := 0
  output := []
  head := fun j => (stk j).length
  tape := fun j => stackTape (stk j)

theorem configuration_bounded (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
    (word : List S) (state : State P) (stk : Fin (k + 1) → List S) (r : ℕ)
    (bound : ∀ j, (stk j).length ≤ r) :
    (bank P entry initial answer).Bounded (decisionData word) r
      (configuration P word.length state stk) := by
  exact ⟨le_rfl, Nat.zero_le _, Nat.zero_le _, by simpa [configuration] using bound⟩

end
end ComplexityOfGenerators.Simulation.StackSpace
