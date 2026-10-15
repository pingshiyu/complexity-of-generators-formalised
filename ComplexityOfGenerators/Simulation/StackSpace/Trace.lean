import ComplexityOfGenerators.Simulation.StackSpace.Native

/-! Composable, space-bounded executions of Mathlib stack programs. These
certificates retain each source step and compile to actual native paths. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing

variable {S Q V : Type} {k : ℕ}

abbrev Source (S Q V : Type) (k : ℕ) := TM2.Cfg (fun _ : Fin (k + 1) => S) Q V

def Within (r : ℕ) (c : Source S Q V k) : Prop := ∀ j, (c.stk j).length ≤ r

inductive Trace (P : Q → Stmt S Q V k) (r : ℕ) : Source S Q V k → Source S Q V k → Prop
  | refl (c) (bound : Within r c) : Trace P r c c
  | step {a b c} (bound : Within r a) (next : TM2.step P a = some b)
      (tail : Trace P r b c) : Trace P r a c

theorem Trace.trans {P : Q → Stmt S Q V k} {r : ℕ} {a b c : Source S Q V k}
    (first : Trace P r a b) (last : Trace P r b c) : Trace P r a c := by
  induction first with
  | refl => exact last
  | step bound next tail ih => exact .step bound next (ih last)

theorem Trace.mono {P : Q → Stmt S Q V k} {r s : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (bound : r ≤ s) : Trace P s a b := by
  induction path with
  | refl c size => exact .refl c (fun j => (size j).trans bound)
  | step size next tail ih => exact .step (fun j => (size j).trans bound) next ih

theorem Trace.reaches {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) : TM2.Reaches P a b := by
  induction path with
  | refl => exact .refl
  | step bound next tail ih => exact Relation.ReflTransGen.head next ih

theorem Trace.end_bound {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) : Within r b := by
  induction path with
  | refl c bound => exact bound
  | step _ _ _ ih => exact ih

theorem Trace.start_bound {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) : Within r a := by
  cases path <;> assumption

/-- Determinism makes every execution from the starting state a prefix of a
terminating trace. Thus a compositional trace proof also bounds all reachable
configurations, as required by the complexity-class interface. -/
theorem Trace.bounds_reachable {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (halted : b.l = none) :
    ∀ c, TM2.Reaches P a c → Within r c := by
  intro c reaches
  have suffix : Trace P r c b := by
    induction reaches with
    | refl => exact path
    | @tail c d reaches next ih =>
        cases ih with
        | refl bound =>
            rcases b with ⟨label, v, stk⟩
            simp only at halted
            subst label
            cases next
        | step bound step rest =>
            have same : _ = d := Option.some.inj (step.symm.trans next)
            subst d
            exact rest
  exact suffix.start_bound

noncomputable section

variable [Fintype Q]

/-- Compile a bounded source trace, including all the intermediate phases
of each stack instruction. -/
theorem Trace.compile {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) (entry : Q) (initial : V) (answer : V → Bool)
    (word : List S) (bits : BitString) :
    ∃ ticks, (bank P entry initial answer).RegionSteps (decisionData word) bits
      (r + programCost P) (ready P word.length a) ticks (ready P word.length b) := by
  induction path with
  | refl c bound =>
      exact ⟨0, .refl _ ((configuration_bounded P entry initial answer word _ _ r bound).mono _ (by omega))⟩
  | @step a b c bound next tail ih =>
      obtain ⟨ticks, first⟩ := step_inRegion P entry initial answer word bits r a b next bound
      obtain ⟨steps, last⟩ := ih
      exact ⟨ticks + steps, first.trans _ last⟩

/-- A complete bounded trace per input suffices: no separate invariant over
arbitrary executions or time bound is needed. -/
theorem mem_pspace_of_trace [Fintype S] [Fintype V]
    (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
    (L : Language S) (space : PolynomialBound)
    (executes : ∀ word, ∃ finish,
      Trace P (space word.length) (sourceInitial entry initial word) finish ∧ finish.l = none ∧
      (answer finish.var = true ↔ word ∈ L)) : L ∈ PSPACE S := by
  apply mem_pspace P entry initial answer L space
  · intro word c reachable
    obtain ⟨finish, path, halted, _⟩ := executes word
    exact path.bounds_reachable halted c reachable
  · intro word
    obtain ⟨finish, path, halted, correct⟩ := executes word
    exact ⟨finish, path.reaches, halted, correct⟩

end
end ComplexityOfGenerators.Simulation.StackSpace
