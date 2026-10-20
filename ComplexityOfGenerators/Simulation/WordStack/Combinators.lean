import ComplexityOfGenerators.Simulation.WordStack.Execution

/-! Finite-control composition. Acceptance returns to the enclosing routine;
every transfer of control is an explicit primitive instruction. -/

namespace ComplexityOfGenerators.Simulation.WordStack

def Instruction.redirect {Q Q' S O : Type} (f : Q → Q') (exit : Instruction Q' S O) :
    Instruction Q S O → Instruction Q' S O
  | .accept => exit
  | .reject => .reject
  | .random no yes => .random (f no) (f yes)
  | .step next action index emit => .step (f next) action index emit

namespace Program

set_option backward.isDefEq.respectTransparency false

variable {Q Q' S O : Type} {k : ℕ} (P : Program Q S O k) (T : Program Q' S O k)

def skip (j : Fin k) : Program Unit S O k where
  initial := ()
  select := fun _ => j
  transition := fun _ _ _ => .accept

theorem skip_returns (j : Fin k) (n : ℕ) (bits : BitString) (m : Memory S O k) :
    (skip j).Returns n bits m 0 m := ⟨(), .refl _, rfl⟩

def atom (j : Fin k) (action : Action S) (index : Move) (emit : Option O) : Program Bool S O k where
  initial := false
  select := fun _ => j
  transition := fun q _ _ => if q then .accept else .step true action index emit

def changeMemory (j : Fin k) (n : ℕ) (action : Action S) (index : Move) (emit : Option O)
    (m : Memory S O k) : Memory S O k :=
  {m with
    indexHead := index.onInput n m.indexHead
    output := m.output ++ emit.toList
    store := Function.update m.store j (action.apply (m.store j))}

theorem atom_returns (j : Fin k) (action : Action S) (index : Move) (emit : Option O)
    (n : ℕ) (bits : BitString) (m : Memory S O k) :
    (atom j action index emit).Returns n bits m 1 (changeMemory j n action index emit m) := by
  refine ⟨true, ?_, rfl⟩
  exact Steps.single _ n bits (m.at false) true action index emit rfl

def sequence : Program (Q ⊕ Q') S O k where
  initial := .inl P.initial
  select := Sum.elim P.select T.select
  transition := fun q cell index => match q with
    | .inl q => Instruction.redirect Sum.inl (.step (.inr T.initial) .stay .stay none)
        (P.transition q cell index)
    | .inr q => Instruction.redirect Sum.inr .accept (T.transition q cell index)

theorem sequence_left : P.Embeds (P.sequence T) Sum.inl := by
  constructor
  · intro q; rfl
  · intro q cell input next action index emit table
    simp only [sequence, table, Instruction.redirect]
  · intro q cell input no yes table
    simp only [sequence, table, Instruction.redirect]

theorem sequence_right : T.Embeds (P.sequence T) Sum.inr := by
  constructor
  · intro q; rfl
  · intro q cell input next action index emit table
    simp only [sequence, table, Instruction.redirect]
  · intro q cell input no yes table
    simp only [sequence, table, Instruction.redirect]

theorem sequence_return {n : ℕ} {bits : BitString} {start middle : Memory S O k}
    {s t : ℕ} {result : Result S O k} (bounded : start.indexHead ≤ n)
    (left : P.Returns n bits start s middle) (right : T.Evaluates n bits middle t result) :
    (P.sequence T).Evaluates n bits start (s + 1 + t) result := by
  have middleBound := left.index_le P bounded
  obtain ⟨q, path, terminal⟩ := left
  have first := (P.sequence_left T).steps P path
  have transfer : (P.sequence T).Steps n bits (middle.at (.inl q)) 1 (middle.at (.inr T.initial)) := by
    apply Steps.go_at _ n bits middle _ _ middleBound
    change Instruction.redirect Sum.inl _ (P.instruction n (middle.at q)) = _
    rw [terminal]; rfl
  cases result with
  | done finish =>
    obtain ⟨r, tail, halt⟩ := right
    refine ⟨.inr r, ((first.trans _ transfer).trans _ ((P.sequence_right T).steps T tail)), ?_⟩
    change Instruction.redirect Sum.inr .accept (T.instruction n (finish.at r)) = _
    rw [halt]; rfl
  | exhausted =>
    exact (first.trans _ transfer).executes _ ((P.sequence_right T).exhausted T right)

theorem sequence_exhausted {n : ℕ} {bits : BitString} {start : Memory S O k} {t : ℕ}
    (left : P.Evaluates n bits start t .exhausted) :
    (P.sequence T).Evaluates n bits start t .exhausted :=
  (P.sequence_left T).exhausted P left

variable {B : Type} {States : B → Type}

/-- Dispatch to one of a finite family of routines after inspecting one stack
head and the index symbol. The family is finite when `B` and its controls are. -/
def branch (j : Fin k) (choose : Option S → Option Unit → B)
    (body : (b : B) → Program (States b) S O k) : Program (Option (Sigma States)) S O k where
  initial := none
  select := fun q => match q with | none => j | some ⟨b, q⟩ => (body b).select q
  transition := fun q cell index => match q with
    | none => let b := choose cell index; .step (some ⟨b, (body b).initial⟩) .stay .stay none
    | some ⟨b, q⟩ => Instruction.redirect (fun q => some ⟨b, q⟩) .accept ((body b).transition q cell index)

theorem branch_body (j : Fin k) (choose : Option S → Option Unit → B)
    (body : (b : B) → Program (States b) S O k) (b : B) :
    (body b).Embeds (branch j choose body) (fun q => some ⟨b, q⟩) := by
  constructor
  · intro q; rfl
  · intro q cell input next action index emit table
    simp only [branch, table, Instruction.redirect]
  · intro q cell input no yes table
    simp only [branch, table, Instruction.redirect]

theorem branch_evaluates (j : Fin k) (choose : Option S → Option Unit → B)
    (body : (b : B) → Program (States b) S O k)
    {n : ℕ} {bits : BitString} {start : Memory S O k} {t : ℕ} {result : Result S O k}
    (bounded : start.indexHead ≤ n)
    (run : (body (choose (start.store j).head? (if start.indexHead < n then some () else none))).Evaluates
      n bits start t result) : (branch j choose body).Evaluates n bits start (1 + t) result := by
  let b := choose (start.store j).head? (if start.indexHead < n then some () else none)
  have first : (branch j choose body).Steps n bits (start.at none) 1 (start.at (some ⟨b, (body b).initial⟩)) := by
    apply Steps.go_at _ n bits start _ _ bounded
    rfl
  cases result with
  | done finish =>
    obtain ⟨q, tail, terminal⟩ := run
    refine ⟨some ⟨b, q⟩, first.trans _ ((branch_body j choose body b).steps _ tail), ?_⟩
    change Instruction.redirect (fun q => (some ⟨b, q⟩ : Option (Sigma States))) .accept ((body b).instruction n (finish.at q)) = _
    rw [terminal]; rfl
  | exhausted => exact first.executes _ ((branch_body j choose body b).exhausted _ run)

def randomChoice {States : Bool → Type} (j : Fin k)
    (body : (b : Bool) → Program (States b) S O k) : Program (Option (Sigma States)) S O k where
  initial := none
  select := fun q => match q with | none => j | some ⟨b, q⟩ => (body b).select q
  transition := fun q cell index => match q with
    | none => .random (some ⟨false, (body false).initial⟩) (some ⟨true, (body true).initial⟩)
    | some ⟨b, q⟩ => Instruction.redirect (fun q => some ⟨b, q⟩) .accept ((body b).transition q cell index)

theorem randomChoice_body {States : Bool → Type} (j : Fin k)
    (body : (b : Bool) → Program (States b) S O k) (b : Bool) :
    (body b).Embeds (randomChoice j body) (fun q => some ⟨b, q⟩) := by
  constructor
  · intro q; rfl
  · intro q cell input next action index emit table
    simp only [randomChoice, table, Instruction.redirect]
  · intro q cell input no yes table
    simp only [randomChoice, table, Instruction.redirect]

def readBit (m : Memory S O k) : Memory S O k := {m with randomHead := m.randomHead + 1}

theorem randomChoice_evaluates {States : Bool → Type} (j : Fin k)
    (body : (b : Bool) → Program (States b) S O k)
    {n : ℕ} {bits : BitString} {start : Memory S O k} {t : ℕ} {result : Result S O k}
    (bit : Bool) (lookup : bits[start.randomHead]? = some bit)
    (run : (body bit).Evaluates n bits (readBit start) t result) :
    (randomChoice j body).Evaluates n bits start (1 + t) result := by
  have first : (randomChoice j body).Steps n bits (start.at none) 1
      ((readBit start).at (some ⟨bit, (body bit).initial⟩)) := by
    apply Steps.random (start.at none) _ _ bit 0 _ rfl lookup
    cases bit <;> exact .refl _
  cases result with
  | done finish =>
    obtain ⟨q, tail, terminal⟩ := run
    refine ⟨some ⟨bit, q⟩, first.trans _ ((randomChoice_body j body bit).steps _ tail), ?_⟩
    change Instruction.redirect (fun q => (some ⟨bit, q⟩ : Option (Sigma States))) .accept ((body bit).instruction n (finish.at q)) = _
    rw [terminal]; rfl
  | exhausted => exact first.executes _ ((randomChoice_body j body bit).exhausted _ run)

theorem randomChoice_exhausted {States : Bool → Type} (j : Fin k)
    (body : (b : Bool) → Program (States b) S O k)
    {n : ℕ} {bits : BitString} (start : Memory S O k) (absent : bits[start.randomHead]? = none) :
    (randomChoice j body).Evaluates n bits start 0 .exhausted :=
  .exhausted _ _ _ rfl absent

def drain (j : Fin k) : Program Unit S O k where
  initial := ()
  select := fun _ => j
  transition := fun _ _ _ => .random () ()

theorem drain_evaluates (j : Fin k) (n : ℕ) (bits : BitString) (start : Memory S O k) :
    (drain j).Evaluates n bits start (bits.length - start.randomHead) .exhausted := by
  generalize equation : bits.length - start.randomHead = remaining
  induction remaining generalizing start with
  | zero =>
    exact .exhausted _ () () rfl (List.getElem?_eq_none (show bits.length ≤ start.randomHead by omega))
  | succ remaining ih =>
    have inside : start.randomHead < bits.length := by omega
    have tail := ih (readBit start) (by simp only [readBit]; omega)
    apply Executes.random _ () () bits[start.randomHead] remaining _ rfl (List.getElem?_eq_getElem inside)
    simpa only [Evaluates, drain, choose, Memory.at, Configuration.mapState, readBit, ite_self] using tail

def loop (j : Fin k) (test : Option S → Option Unit → Bool) : Program (Option Q) S O k where
  initial := none
  select := fun q => match q with | none => j | some q => P.select q
  transition := fun q cell index => match q with
    | none => if test cell index then .step (some P.initial) .stay .stay none else .accept
    | some q => Instruction.redirect some (.step none .stay .stay none) (P.transition q cell index)

theorem loop_body (j : Fin k) (test : Option S → Option Unit → Bool) :
    P.Embeds (P.loop j test) some := by
  constructor
  · intro q; rfl
  · intro q cell input next action index emit table
    simp only [loop, table, Instruction.redirect]
  · intro q cell input no yes table
    simp only [loop, table, Instruction.redirect]

theorem loop_stop (j : Fin k) (test : Option S → Option Unit → Bool)
    {n : ℕ} {bits : BitString} (start : Memory S O k)
    (stop : test (start.store j).head? (if start.indexHead < n then some () else none) = false) :
    (P.loop j test).Returns n bits start 0 start := by
  refine ⟨none, .refl _, ?_⟩
  simp only [instruction, Memory.at, Configuration.mapState, loop]
  rw [stop]; rfl

theorem loop_return (j : Fin k) (test : Option S → Option Unit → Bool)
    {n : ℕ} {bits : BitString} {start middle : Memory S O k} {s t : ℕ} {result : Result S O k}
    (bounded : start.indexHead ≤ n)
    (again : test (start.store j).head? (if start.indexHead < n then some () else none) = true)
    (body : P.Returns n bits start s middle) (rest : (P.loop j test).Evaluates n bits middle t result) :
    (P.loop j test).Evaluates n bits start (1 + s + 1 + t) result := by
  have first : (P.loop j test).Steps n bits (start.at none) 1 (start.at (some P.initial)) := by
    apply Steps.go_at _ n bits start _ _ bounded
    simp only [instruction, Memory.at, Configuration.mapState, loop]
    rw [again]; rfl
  have middleBound := body.index_le P bounded
  obtain ⟨q, path, terminal⟩ := body
  have middlePath := (P.loop_body j test).steps P path
  have transfer : (P.loop j test).Steps n bits (middle.at (some q)) 1 (middle.at none) := by
    apply Steps.go_at _ n bits middle _ _ middleBound
    change Instruction.redirect some _ (P.instruction n (middle.at q)) = _
    rw [terminal]; rfl
  have segment := (first.trans _ middlePath).trans _ transfer
  cases result with
  | done finish =>
    obtain ⟨r, tail, halt⟩ := rest
    exact ⟨r, segment.trans _ tail, halt⟩
  | exhausted => exact segment.executes _ rest

theorem loop_exhausted (j : Fin k) (test : Option S → Option Unit → Bool)
    {n : ℕ} {bits : BitString} {start : Memory S O k} {t : ℕ}
    (bounded : start.indexHead ≤ n)
    (again : test (start.store j).head? (if start.indexHead < n then some () else none) = true)
    (body : P.Evaluates n bits start t .exhausted) :
    (P.loop j test).Evaluates n bits start (1 + t) .exhausted := by
  have first : (P.loop j test).Steps n bits (start.at none) 1 (start.at (some P.initial)) := by
    apply Steps.go_at _ n bits start _ _ bounded
    simp only [instruction, Memory.at, Configuration.mapState, loop]
    rw [again]; rfl
  exact first.executes _ ((P.loop_body j test).exhausted P body)

end Program
end ComplexityOfGenerators.Simulation.WordStack
