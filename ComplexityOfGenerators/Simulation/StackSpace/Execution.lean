import ComplexityOfGenerators.Simulation.StackSpace.Instructions

/-!
# Compiling complete Mathlib stack-machine steps

One source step is a finite syntax tree. Its native tape-bank implementation
takes at most `cost` transitions. This bound depends only on program text,
not the stack lengths, input or number of search iterations.
-/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Fintype Q]
variable (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
variable (word : List S) (bits : BitString)

def cost : Stmt S Q V k → ℕ
  | .push _ _ a | .pop _ _ a | .peek _ _ a | .load _ a => 2 + cost a
  | .branch _ a b => 2 + cost a + cost b
  | .goto _ | .halt => 1

def ready (P : Q → Stmt S Q V k) (n : ℕ) (c : TM2.Cfg (fun _ : Fin (k + 1) => S) Q V) : Config P :=
  configuration P n (match c.l with | none => .halt c.var | some q => .exec (node P q) c.var) c.stk

local notation "B" => bank P entry initial answer
local notation "C" => configuration P word.length
local notation "D" => decisionData word

theorem execute (a : Stmt S Q V k) (ha : a ∈ statements P)
    (v : V) (stk : Fin (k + 1) → List S) :
    ∃ t ≤ cost a, (B).Steps D bits (C (.exec ⟨a, ha⟩ v) stk) t
      (ready P word.length (TM2.stepAux a v stk)) := by
  classical
  induction a generalizing v stk with
  | push j f a ih =>
      obtain ⟨t, bound, tail⟩ := ih (substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])) v
        (Function.update stk j (f v :: stk j))
      exact ⟨1 + t, by simp only [cost]; omega,
        (push P entry initial answer word bits j f a ha v stk).trans B tail⟩
  | pop j f a ih =>
      obtain ⟨t, bound, tail⟩ := ih (substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])) (f v (stk j).head?)
        (Function.update stk j (stk j).tail)
      obtain ⟨s, sbound, first⟩ := pop P entry initial answer word bits j f a ha v stk
      exact ⟨s + t, by simp only [cost]; omega, first.trans B tail⟩
  | peek j f a ih =>
      obtain ⟨t, bound, tail⟩ := ih (substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])) (f v (stk j).head?) stk
      obtain ⟨s, sbound, first⟩ := peek P entry initial answer word bits j f a ha v stk
      exact ⟨s + t, by simp only [cost]; omega, first.trans B tail⟩
  | load f a ih =>
      obtain ⟨t, bound, tail⟩ := ih (substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])) (f v) stk
      have first := go P entry initial answer word bits (.exec ⟨.load f a, ha⟩ v)
        (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v)) stk (by
          simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected])
      exact ⟨1 + t, by simp only [cost]; omega, first.trans B tail⟩
  | branch f a b iha ihb =>
      cases h : f v with
      | false =>
          obtain ⟨t, bound, tail⟩ := ihb (substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])) v stk
          have first := go P entry initial answer word bits (.exec ⟨.branch f a b, ha⟩ v)
            (.exec ⟨b, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v) stk (by
              simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected, h])
          exact ⟨1 + t, by simp only [cost]; omega, by simpa [TM2.stepAux, h] using first.trans B tail⟩
      | true =>
          obtain ⟨t, bound, tail⟩ := iha (substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])) v stk
          have first := go P entry initial answer word bits (.exec ⟨.branch f a b, ha⟩ v)
            (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v) stk (by
              simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected, h])
          exact ⟨1 + t, by simp only [cost]; omega, by simpa [TM2.stepAux, h] using first.trans B tail⟩
  | goto f =>
      refine ⟨1, le_rfl, go P entry initial answer word bits _ _ stk ?_⟩
      simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected]
  | halt =>
      refine ⟨1, le_rfl, go P entry initial answer word bits _ _ stk ?_⟩
      simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected]

/-- A uniform constant for all source steps, including nested instructions. -/
def programCost (P : Q → Stmt S Q V k) : ℕ := Finset.univ.sup fun q => cost (P q)

theorem cost_le_programCost (q : Q) : cost (P q) ≤ programCost P :=
  Finset.le_sup (f := fun q => cost (P q)) (Finset.mem_univ q)

/-- A source step with stacks of length at most `s` never leaves radius
`s + programCost P`, including all temporary compiler phases. -/
theorem step_inRegion (s : ℕ) (c d : TM2.Cfg (fun _ : Fin (k + 1) => S) Q V)
    (step : TM2.step P c = some d) (bound : ∀ j, (c.stk j).length ≤ s) :
    ∃ t, (B).RegionSteps D bits (s + programCost P) (ready P word.length c) t (ready P word.length d) := by
  rcases c with ⟨label, v, stk⟩
  cases label with
  | none => simp [TM2.step] at step
  | some q =>
      have hd : TM2.stepAux (P q) v stk = d := Option.some.inj step
      obtain ⟨t, time, path⟩ := execute P entry initial answer word bits (P q) (statement_mem P q) v stk
      rw [hd] at path
      exact ⟨t, (path.inRegion B s
        (configuration_bounded P entry initial answer word _ _ s bound)).mono B
          (Nat.add_le_add_left (time.trans (cost_le_programCost P q)) s)⟩

end
end ComplexityOfGenerators.Simulation.StackSpace
