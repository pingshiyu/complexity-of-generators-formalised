import ComplexityOfGenerators.Simulation.WordStack.Words

/-! Finite straight-line stack routines. Their semantic evaluator is justified
by primitive command executions, with a constant bound on their running time. -/

namespace ComplexityOfGenerators.Simulation.WordStack

inductive Local (S : Type) (k : ℕ)
  | skip
  | act (stack : Fin k) (action : Action S)
  | read (stack : Fin k) (next : Option S → Local S k)
  | seq (first second : Local S k)

namespace Local

variable {S O : Type} {k : ℕ}

abbrev Store (S : Type) (k : ℕ) := Fin k → List S

def eval : Local S k → Store S k → Store S k
  | .skip, s => s
  | .act j a, s => Function.update s j (a.apply (s j))
  | .read j next, s => (next (s j).head?).eval s
  | .seq a b, s => b.eval (a.eval s)

@[simp] theorem eval_skip (s : Store S k) : (Local.skip).eval s = s := rfl
@[simp] theorem eval_seq (a b : Local S k) (s : Store S k) : (a.seq b).eval s = b.eval (a.eval s) := rfl
@[simp] theorem eval_read (j : Fin k) (next : Option S → Local S k) (s : Store S k) :
    (Local.read j next).eval s = (next (s j).head?).eval s := rfl

def ticks : Local S k → Store S k → ℕ
  | .skip, _ => 0
  | .act .., _ => 1
  | .read j next, s => 1 + (next (s j).head?).ticks s
  | .seq a b, s => a.ticks s + 1 + b.ticks (a.eval s)

noncomputable def bound [Fintype S] : Local S k → ℕ
  | .skip => 0
  | .act .. => 1
  | .read _ next => 1 + Finset.univ.sup (fun o => (next o).bound)
  | .seq a b => a.bound + 1 + b.bound

theorem ticks_le [Fintype S] (c : Local S k) (s : Store S k) : c.ticks s ≤ c.bound := by
  induction c generalizing s with
  | skip => rfl
  | act => rfl
  | read j next ih =>
    apply Nat.add_le_add_left
    exact (ih (s j).head? s).trans (Finset.le_sup (f := fun o => (next o).bound) (Finset.mem_univ (s j).head?))
  | seq a b ha hb => exact Nat.add_le_add (Nat.add_le_add_right (ha s) 1) (hb (a.eval s))

def command : Local S k → Command S O k
  | .skip => .skip
  | .act j a => .act j a .stay none
  | .read j next => .branch j (fun o => (next o.1).command)
  | .seq a b => a.command.seq b.command

def apply (c : Local S k) (m : Memory S O k) : Memory S O k := {m with store := c.eval m.store}

@[simp] theorem apply_index (c : Local S k) (m : Memory S O k) : (c.apply m).indexHead = m.indexHead := rfl
@[simp] theorem apply_random (c : Local S k) (m : Memory S O k) : (c.apply m).randomHead = m.randomHead := rfl
@[simp] theorem apply_output (c : Local S k) (m : Memory S O k) : (c.apply m).output = m.output := rfl
@[simp] theorem apply_store (c : Local S k) (m : Memory S O k) : (c.apply m).store = c.eval m.store := rfl

theorem runs (c : Local S k) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    c.command.Runs n bits m (c.ticks m.store) (.done (c.apply m)) := by
  induction c generalizing m with
  | skip => exact Command.Runs.skip m
  | act j a => exact Command.act_stay j a bits m bounded
  | read j next ih => exact Command.Runs.branch m j _ _ _ (ih _ m bounded)
  | seq a b ha hb => exact Command.Runs.seq m (a.apply m) _ _ _ _ _ (ha m bounded) (hb _ bounded)

def push (j : Fin k) (a : S) : Local S k := .act j (.push a)
def pop (j : Fin k) : Local S k := .act j .pop
def write (j : Fin k) (a : S) : Local S k := (pop j).seq (push j a)

@[simp] theorem eval_push (j : Fin k) (a : S) (s : Store S k) :
    (push j a).eval s = Function.update s j (a :: s j) := rfl
@[simp] theorem eval_pop (j : Fin k) (s : Store S k) :
    (pop j).eval s = Function.update s j (s j).tail := rfl
@[simp] theorem eval_write (j : Fin k) (a : S) (s : Store S k) :
    (write j a).eval s = Function.update s j (a :: (s j).tail) := by
  simp [write, eval, pop, push, Action.apply, Function.update_idem]

/-- Move a single symbol between stacks, optionally supplying a blank. -/
def moveOne (src dst : Fin k) (fallback : Option S) : Local S k :=
  .read src fun head => match head with
    | some a => (pop src).seq (push dst a)
    | none => match fallback with | none => .skip | some a => push dst a

def moveRead (left right : Fin k) : Move → Local S k
  | .stay => .skip
  | .left => moveOne left right none
  | .right => moveOne right left none

def moveWork (left right : Fin k) (blank : S) : Move → Local S k
  | .stay => .skip
  | .left => moveOne left right (some blank)
  | .right => moveOne right left (some blank)

end Local
end ComplexityOfGenerators.Simulation.WordStack
