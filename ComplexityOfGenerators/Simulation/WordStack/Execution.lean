import ComplexityOfGenerators.Simulation.WordStack.Basic

/-! Finite execution segments and control-state embeddings for stack programs.
These support composition without clearing or treating a word as one machine
instruction. -/

namespace ComplexityOfGenerators.Simulation.WordStack

def Configuration.mapState {Q Q' S O : Type} {k : ℕ} (f : Q → Q')
    (c : Configuration Q S O k) : Configuration Q' S O k :=
  ⟨f c.state, c.indexHead, c.randomHead, c.output, c.store⟩

@[simp] theorem Configuration.mapState_id {Q S O : Type} {k : ℕ}
    (c : Configuration Q S O k) : c.mapState id = c := rfl

@[simp] theorem Configuration.mapState_comp {Q Q' Q'' S O : Type} {k : ℕ}
    (f : Q → Q') (g : Q' → Q'') (c : Configuration Q S O k) :
    (c.mapState f).mapState g = c.mapState (g ∘ f) := rfl

/-- Data shared by consecutive routines, without a control-state component. -/
abbrev Memory (S O : Type) (k : ℕ) := Configuration Unit S O k

def Memory.at {Q S O : Type} {k : ℕ} (m : Memory S O k) (q : Q) : Configuration Q S O k :=
  m.mapState (fun _ => q)

@[simp] theorem Memory.map_at {Q Q' S O : Type} {k : ℕ} (m : Memory S O k) (q : Q) (f : Q → Q') :
    (m.at q).mapState f = m.at (f q) := rfl

inductive Result (S O : Type) (k : ℕ)
  | done (memory : Memory S O k)
  | exhausted

def Result.outcome {S O : Type} {k : ℕ} : Result S O k → Outcome O
  | .done m => .accepted m.output
  | .exhausted => .exhausted

namespace Program

variable {Q S O : Type} {k : ℕ} (P : Program Q S O k)

inductive Steps (n : ℕ) (bits : BitString) :
    Configuration Q S O k → ℕ → Configuration Q S O k → Prop
  | refl (c) : Steps n bits c 0 c
  | random (c) (no yes : Q) (bit : Bool) (t d)
      (table : P.instruction n c = .random no yes) (lookup : bits[c.randomHead]? = some bit)
      (rest : Steps n bits (choose c (if bit then yes else no)) t d) :
      Steps n bits c (t + 1) d
  | step (c) (next action index emit) (t d)
      (table : P.instruction n c = .step next action index emit)
      (rest : Steps n bits (P.advance n c next action index emit) t d) :
      Steps n bits c (t + 1) d

theorem Steps.single (n : ℕ) (bits : BitString) (c : Configuration Q S O k)
    (next action index emit) (table : P.instruction n c = .step next action index emit) :
    P.Steps n bits c 1 (P.advance n c next action index emit) :=
  .step c next action index emit 0 _ table (.refl _)

theorem advance_go (n : ℕ) (c : Configuration Q S O k) (next : Q)
    (bounded : c.indexHead ≤ n) :
    P.advance n c next .stay .stay none = {c with state := next} := by
  simp [advance, Action.apply, Move.onInput, Nat.min_eq_left bounded,
    Function.update_eq_self]

theorem Steps.go (n : ℕ) (bits : BitString) (c : Configuration Q S O k) (next : Q)
    (bounded : c.indexHead ≤ n)
    (table : P.instruction n c = .step next .stay .stay none) :
    P.Steps n bits c 1 {c with state := next} := by
  simpa only [P.advance_go n c next bounded] using Steps.single P n bits c _ _ _ _ table

theorem Steps.go_at (n : ℕ) (bits : BitString) (m : Memory S O k) (q next : Q)
    (bounded : m.indexHead ≤ n)
    (table : P.instruction n (m.at q) = .step next .stay .stay none) :
    P.Steps n bits (m.at q) 1 (m.at next) := by
  simpa only [Memory.at, Configuration.mapState] using
    Steps.go P n bits (m.at q) next bounded table

theorem Steps.trans {n : ℕ} {bits : BitString} {a b c : Configuration Q S O k} {s t : ℕ}
    (left : P.Steps n bits a s b) (right : P.Steps n bits b t c) : P.Steps n bits a (s + t) c := by
  induction left with
  | refl => simpa using right
  | random a no yes bit s b table lookup rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Steps.random a no yes bit (s + t) c table lookup (ih right)
  | step a next action index emit s b table rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Steps.step a next action index emit (s + t) c table (ih right)

theorem Steps.executes {n : ℕ} {bits : BitString} {a b : Configuration Q S O k} {s t : ℕ}
    {result : Outcome O} (path : P.Steps n bits a s b) (halt : P.Executes n bits b t result) :
    P.Executes n bits a (s + t) result := by
  induction path with
  | refl => simpa using halt
  | random a no yes bit s b table lookup rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Executes.random a no yes bit (s + t) result table lookup (ih halt)
  | step a next action index emit s b table rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Executes.step a next action index emit (s + t) result table (ih halt)

theorem Steps.index_le {n : ℕ} {bits : BitString} {a b : Configuration Q S O k} {t : ℕ}
    (path : P.Steps n bits a t b) (bounded : a.indexHead ≤ n) : b.indexHead ≤ n := by
  induction path with
  | refl => exact bounded
  | random a no yes bit t b table lookup rest ih => exact ih bounded
  | step a next action index emit t b table rest ih => exact ih (index.onInput_le _ _ bounded)

/-- An embedding preserves every nonterminal primitive instruction. Source
acceptance may instead transfer control to another routine in the target. -/
structure Embeds {Q' : Type} (T : Program Q' S O k) (f : Q → Q') : Prop where
  select : ∀ q, T.select (f q) = P.select q
  step : ∀ q cell input next action index emit,
    P.transition q cell input = .step next action index emit →
    T.transition (f q) cell input = .step (f next) action index emit
  random : ∀ q cell input no yes, P.transition q cell input = .random no yes →
    T.transition (f q) cell input = .random (f no) (f yes)

theorem Embeds.advance {Q' : Type} {T : Program Q' S O k} {f : Q → Q'}
    (embedding : P.Embeds T f) (n : ℕ) (c : Configuration Q S O k)
    (next action index emit) :
    T.advance n (c.mapState f) (f next) action index emit =
      (P.advance n c next action index emit).mapState f := by
  simp [Program.advance, Configuration.mapState, embedding.select]

theorem Embeds.steps {Q' : Type} {T : Program Q' S O k} {f : Q → Q'}
    (embedding : P.Embeds T f) {n : ℕ} {bits : BitString}
    {a b : Configuration Q S O k} {t : ℕ} (path : P.Steps n bits a t b) :
    T.Steps n bits (a.mapState f) t (b.mapState f) := by
  induction path with
  | refl c => exact .refl _
  | random c no yes bit t d table lookup rest ih =>
    apply Steps.random _ (f no) (f yes) bit t _
    · simp only [instruction, Configuration.mapState, embedding.select]
      exact embedding.random _ _ _ _ _ table
    · exact lookup
    · simpa only [choose, Configuration.mapState, apply_ite f] using ih
  | step c next action index emit t d table rest ih =>
    apply Steps.step _ (f next) action index emit t _
    · simp only [instruction, Configuration.mapState, embedding.select]
      exact embedding.step _ _ _ _ _ _ _ table
    · rwa [embedding.advance]

theorem Embeds.exhausted {Q' : Type} {T : Program Q' S O k} {f : Q → Q'}
    (embedding : P.Embeds T f) {n : ℕ} {bits : BitString}
    {c : Configuration Q S O k} {t : ℕ} (exec : P.Executes n bits c t .exhausted) :
    T.Executes n bits (c.mapState f) t .exhausted := by
  generalize equality : Outcome.exhausted = result at exec
  induction exec with
  | accept c table => cases equality
  | reject c table => cases equality
  | exhausted c no yes table absent =>
    apply Executes.exhausted _ (f no) (f yes)
    · simp only [instruction, Configuration.mapState, embedding.select]
      exact embedding.random _ _ _ _ _ table
    · exact absent
  | random c no yes bit t result table lookup rest ih =>
    apply Executes.random _ (f no) (f yes) bit t _
    · simp only [instruction, Configuration.mapState, embedding.select]
      exact embedding.random _ _ _ _ _ table
    · exact lookup
    · simpa only [choose, Configuration.mapState, apply_ite f] using ih equality
  | step c next action index emit t result table rest ih =>
    apply Executes.step _ (f next) action index emit t _
    · simp only [instruction, Configuration.mapState, embedding.select]
      exact embedding.step _ _ _ _ _ _ _ table
    · rw [embedding.advance]
      exact ih equality

/-- A successful routine exposes its final memory to the next routine. -/
def Returns (n : ℕ) (bits : BitString) (start : Memory S O k) (t : ℕ) (finish : Memory S O k) : Prop :=
  ∃ q, P.Steps n bits (start.at P.initial) t (finish.at q) ∧ P.instruction n (finish.at q) = .accept

def Evaluates (n : ℕ) (bits : BitString) (start : Memory S O k) (t : ℕ) : Result S O k → Prop
  | .done finish => P.Returns n bits start t finish
  | .exhausted => P.Executes n bits (start.at P.initial) t .exhausted

theorem Returns.executes {n : ℕ} {bits : BitString} {start finish : Memory S O k} {t : ℕ}
    (run : P.Returns n bits start t finish) :
    P.Executes n bits (start.at P.initial) t (.accepted finish.output) := by
  obtain ⟨q, path, terminal⟩ := run
  simpa only [Nat.add_zero, Memory.at, Configuration.mapState] using path.executes P (.accept _ terminal)

theorem Returns.index_le {n : ℕ} {bits : BitString} {start finish : Memory S O k} {t : ℕ}
    (run : P.Returns n bits start t finish) (bounded : start.indexHead ≤ n) : finish.indexHead ≤ n := by
  obtain ⟨q, path, _⟩ := run
  exact path.index_le P bounded

theorem Evaluates.executes {n : ℕ} {bits : BitString} {start : Memory S O k} {t : ℕ}
    {result : Result S O k} (run : P.Evaluates n bits start t result) :
    P.Executes n bits (start.at P.initial) t result.outcome := by
  cases result with
  | done finish => exact Returns.executes P run
  | exhausted => exact run

end Program
end ComplexityOfGenerators.Simulation.WordStack
