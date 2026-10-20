import ComplexityOfGenerators.Simulation.LibraryTM.Tape

/-! A uniform finite program for library deterministic machines. It copies the
input once, reads all virtual heads into finite control, and commits the source
action one tape at a time. Input and output occupy charged virtual tapes. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM

open TransducerBank
set_option backward.isDefEq.respectTransparency false

inductive Phase (Q : Type) (k : ℕ)
  | start | load | rewind
  | gather (q : Q) (cursor : Fin (k + 1)) (symbols : Fin k → Complexity.Γ)
  | commit (q : Q) (cursor : Fin (k + 1)) (actions : Fin k → Complexity.Γ × Complexity.Dir3)
  | verdictOrigin | verdictStep | verdict
  deriving Fintype

variable {n : ℕ} (M : Complexity.TM n)

abbrev State := Phase M.Q (n + 2)
abbrev Config := BankConfiguration Unit (State M) Complexity.Γ (n + 2)

def tapes (c : Complexity.Cfg n M.Q) : Fin (n + 2) → Complexity.Tape :=
  Fin.cases c.input (Fin.lastCases c.output c.work)

def action (q : M.Q) (symbols : Fin (n + 2) → Complexity.Γ) :
    M.Q × (Fin (n + 2) → Complexity.Γ × Complexity.Dir3) :=
  let a := M.δ q (symbols 0) (fun i => symbols i.castSucc.succ) (symbols (Fin.last n).succ)
  (a.1, Fin.cases (symbols 0, a.2.2.2.1)
    (Fin.lastCases (a.2.2.1.toΓ, a.2.2.2.2.2)
      (fun i => ((a.2.1 i).toΓ, a.2.2.2.2.1 i))))

def ready (q : M.Q) : State M := .gather q 0 (fun _ => .blank)

def select : State M → Fin (n + 2)
  | .gather _ j _ | .commit _ j _ => if h : j.val < n + 2 then ⟨j.val, h⟩ else 0
  | .verdictOrigin | .verdictStep | .verdict => (Fin.last n).succ
  | _ => 0

def transition (phase : State M) (input : Option Bool) (origin : Bool) (cell : Complexity.Γ) :
    BankInstruction (State M) Complexity.Γ Unit :=
  let go := fun state symbol direction =>
    BankInstruction.step state symbol direction .stay .stay .stay none
  match phase with
  | .start => go .load cell .right
  | .load => match input with
      | some bit => .step .load (Complexity.Γ.ofBool bit) .right .right .stay .stay none
      | none => go .rewind cell .stay
  | .rewind => go (if origin then ready M M.qstart else .rewind) cell
      (if origin then .stay else .left)
  | .gather q j symbols =>
      if q = M.qhalt then go .verdictOrigin cell .stay
      else if h : j.val < n + 2 then
        go (.gather q ⟨j.val + 1, by omega⟩
          (Function.update symbols ⟨j.val, h⟩ (read origin cell))) cell .stay
      else
        let a := action M q symbols
        go (.commit a.1 0 a.2) cell .stay
  | .commit q j actions =>
      if h : j.val < n + 2 then
        let a := actions ⟨j.val, h⟩
        go (.commit q ⟨j.val + 1, by omega⟩ actions) (write origin a.1) (move origin a.2)
      else go (ready M q) cell .stay
  | .verdictOrigin => go (if origin then .verdictStep else .verdictOrigin) cell
      (if origin then .stay else .left)
  | .verdictStep => go .verdict cell .right
  | .verdict => if cell = .one then .accept else .reject

def bank : TapeBank Bool Bool Unit (State M) Complexity.Γ (n + 2) where
  initial := .start
  blank := .blank
  select := select M
  transition := fun phase input _ _ origin cell => transition M phase input origin cell

theorem deterministic : (bank M).Deterministic := by
  intro phase input auxiliary index origin cell
  cases phase <;> cases input <;> simp only [bank, transition]
  all_goals split_ifs <;> trivial

/-- Native read-only heads stay at the end of the copied input during simulation. -/
def encoded (word : BitString) (phase : State M) (ts : Fin (n + 2) → Complexity.Tape) : Config M :=
  ⟨phase, word.length, 0, 0, 0, [], fun j => (ts j).head, fun j => image (ts j)⟩

def configuration (word : BitString) (c : Complexity.Cfg n M.Q) : Config M :=
  encoded M word (ready M c.state) (tapes M c)

end ComplexityOfGenerators.Simulation.LibraryTM
