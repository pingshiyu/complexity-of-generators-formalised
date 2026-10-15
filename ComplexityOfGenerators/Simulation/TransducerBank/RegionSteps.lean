import ComplexityOfGenerators.Simulation.TransducerBank.Space

/-! Composable tape-bank paths whose intermediate heads stay in a fixed region.
Small routines may use a time bound to establish a region bound, then repeat
arbitrarily often within that same region. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem Bounded.mono {data : InputData I A} {r s : ℕ} {c : BankConfiguration O Q S k}
    (h : B.Bounded data r c) (bound : r ≤ s) : B.Bounded data s c :=
  ⟨h.input, h.auxiliary, h.index, fun j => (h.head j).trans bound⟩

theorem Bounded.with_state {data : InputData I A} {r : ℕ} {c : BankConfiguration O Q S k}
    (h : B.Bounded data r c) (state : Q) : B.Bounded data r {c with state := state} :=
  ⟨h.input, h.auxiliary, h.index, h.head⟩

inductive RegionSteps (data : InputData I A) (bits : BitString) (r : ℕ) :
    BankConfiguration O Q S k → ℕ → BankConfiguration O Q S k → Prop
  | refl (c) (bounded : B.Bounded data r c) : RegionSteps data bits r c 0 c
  | random (c) (no yes : Q) (bit : Bool) (t d)
      (bounded : B.Bounded data r c)
      (table : B.instruction data c = .readRandom no yes) (lookup : bits[c.randomHead]? = some bit)
      (rest : RegionSteps data bits r (choose c (if bit then yes else no)) t d) :
      RegionSteps data bits r c (t + 1) d
  | step (c) (next write work input auxiliary index emit) (t d)
      (bounded : B.Bounded data r c)
      (table : B.instruction data c = .step next write work input auxiliary index emit)
      (rest : RegionSteps data bits r (B.advance data c next write work input auxiliary index emit) t d) :
      RegionSteps data bits r c (t + 1) d

theorem RegionSteps.start_bound {data : InputData I A} {bits : BitString} {r t : ℕ}
    {a b : BankConfiguration O Q S k} (path : B.RegionSteps data bits r a t b) :
    B.Bounded data r a := by cases path <;> assumption

theorem RegionSteps.end_bound {data : InputData I A} {bits : BitString} {r t : ℕ}
    {a b : BankConfiguration O Q S k} (path : B.RegionSteps data bits r a t b) :
    B.Bounded data r b := by
  induction path with
  | refl c bound => exact bound
  | random _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem RegionSteps.toSteps {data : InputData I A} {bits : BitString} {r t : ℕ}
    {a b : BankConfiguration O Q S k} (path : B.RegionSteps data bits r a t b) :
    B.Steps data bits a t b := by
  induction path with
  | refl c bound => exact .refl c
  | random c no yes bit t d bound table lookup rest ih => exact .random c no yes bit t d table lookup ih
  | step c next write work input auxiliary index emit t d bound table rest ih =>
      exact .step c next write work input auxiliary index emit t d table ih

theorem RegionSteps.mono {data : InputData I A} {bits : BitString} {r s t : ℕ}
    {a b : BankConfiguration O Q S k} (path : B.RegionSteps data bits r a t b) (bound : r ≤ s) :
    B.RegionSteps data bits s a t b := by
  induction path with
  | refl c bounded => exact .refl c (bounded.mono B bound)
  | random c no yes bit t d bounded table lookup rest ih =>
      exact .random c no yes bit t d (bounded.mono B bound) table lookup ih
  | step c next write work input auxiliary index emit t d bounded table rest ih =>
      exact .step c next write work input auxiliary index emit t d (bounded.mono B bound) table ih

theorem RegionSteps.trans {data : InputData I A} {bits : BitString} {r s t : ℕ}
    {a b c : BankConfiguration O Q S k} (left : B.RegionSteps data bits r a s b)
    (right : B.RegionSteps data bits r b t c) : B.RegionSteps data bits r a (s + t) c := by
  induction left with
  | refl => simpa using right
  | random a no yes bit s b bound table lookup rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RegionSteps.random a no yes bit (s + t) c bound table lookup (ih right)
  | step a next write work input auxiliary index emit s b bound table rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RegionSteps.step a next write work input auxiliary index emit (s + t) c bound table (ih right)

/-- A short routine beginning at radius `r` stays within `r+t`. The resulting
region paths can be composed without adding their lengths to the radius. -/
theorem Steps.inRegion {data : InputData I A} {bits : BitString} {t : ℕ}
    {a b : BankConfiguration O Q S k} (path : B.Steps data bits a t b)
    (r : ℕ) (bounded : B.Bounded data r a) : B.RegionSteps data bits (r + t) a t b := by
  induction path generalizing r with
  | refl c => simpa using RegionSteps.refl c bounded
  | random c no yes bit t d table lookup rest ih =>
      apply RegionSteps.random c no yes bit t d (bounded.mono B (by omega)) table lookup
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (r + 1) (B.choose_bounded data r c _ bounded)
  | step c next write work input auxiliary index emit t d table rest ih =>
      apply RegionSteps.step c next write work input auxiliary index emit t d
        (bounded.mono B (by omega)) table
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (r + 1) (B.advance_bounded data r c next write work input auxiliary index emit bounded)

/-- A complete execution whose entire path stays in one fixed region. -/
def RegionRun (data : InputData I A) (bits : BitString) (r : ℕ)
    (start : BankConfiguration O Q S k) (result : Outcome O) : Prop :=
  ∃ ticks finish, B.RegionSteps data bits r start ticks finish ∧
    B.Executes data bits finish 0 result

theorem RegionRun.mono {data : InputData I A} {bits : BitString} {r s : ℕ}
    {start : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.RegionRun data bits r start result) (bound : r ≤ s) :
    B.RegionRun data bits s start result := by
  obtain ⟨ticks, finish, path, halt⟩ := run
  exact ⟨ticks, finish, path.mono B bound, halt⟩

theorem RegionRun.prepend {data : InputData I A} {bits : BitString} {r t : ℕ}
    {start middle : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.RegionRun data bits r middle result) (path : B.RegionSteps data bits r start t middle) :
    B.RegionRun data bits r start result := by
  obtain ⟨ticks, finish, tail, halt⟩ := run
  exact ⟨t + ticks, finish, path.trans B tail, halt⟩

theorem RegionRun.executes {data : InputData I A} {bits : BitString} {r : ℕ}
    {start : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.RegionRun data bits r start result) : ∃ ticks, B.Executes data bits start ticks result := by
  obtain ⟨ticks, finish, path, halt⟩ := run
  exact ⟨ticks, by simpa using (path.toSteps B).executes B halt⟩

theorem Executes.path {data : InputData I A} {bits : BitString} {t : ℕ}
    {start : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.Executes data bits start t result) :
    ∃ finish, B.Steps data bits start t finish ∧ B.Executes data bits finish 0 result := by
  induction run with
  | accept c table => exact ⟨c, .refl c, .accept c table⟩
  | reject c table => exact ⟨c, .refl c, .reject c table⟩
  | exhausted c no yes table absent => exact ⟨c, .refl c, .exhausted c no yes table absent⟩
  | random c no yes bit t result table lookup rest ih =>
      obtain ⟨finish, path, halt⟩ := ih
      exact ⟨finish, .random c no yes bit t finish table lookup path, halt⟩
  | step c next write work input auxiliary index emit t result table rest ih =>
      obtain ⟨finish, path, halt⟩ := ih
      exact ⟨finish, .step c next write work input auxiliary index emit t finish table path, halt⟩

theorem Executes.inRegion {data : InputData I A} {bits : BitString} {t r : ℕ}
    {start : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.Executes data bits start t result) (bound : B.Bounded data r start) :
    B.RegionRun data bits (r + t) start result := by
  obtain ⟨finish, path, halt⟩ := run.path B
  exact ⟨t, finish, path.inRegion B r bound, halt⟩

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

theorem TapeBank.RegionSteps.compile {data : InputData I A} {bits : BitString} {r t : ℕ}
    {a b : BankConfiguration O Q S k} (path : B.RegionSteps data bits r a t b)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (ready : BankReady B a negative start) (region : (bankMachine B).InRegion r start) :
    ∃ ticks finish sides, BankReady B b sides finish ∧
      (bankMachine B).Steps data bits start ticks finish ∧ (bankMachine B).InRegion r finish := by
  induction path generalizing negative start with
  | refl c bound => exact ⟨0, start, negative, ready, .refl, region⟩
  | random c no yes bit t d bound table lookup rest ih =>
      obtain ⟨ticks, middle, _, related, first, bounded⟩ :=
        bank_random_inRegion B data bits r c negative start ready bound no yes bit table lookup region
      obtain ⟨remaining, finish, sides, related, tail, visited⟩ := ih negative middle related bounded
      exact ⟨ticks + remaining, finish, sides, related, first.trans _ tail, visited⟩
  | step c next write work input auxiliary index emit t d bound table rest ih =>
      obtain ⟨ticks, middle, sides, _, related, first, bounded⟩ :=
        bank_step_inRegion B data bits r c negative start ready bound next write work input auxiliary index emit
          table region (rest.start_bound B)
      obtain ⟨remaining, finish, sides, related, tail, visited⟩ := ih sides middle related bounded
      exact ⟨ticks + remaining, finish, sides, related, first.trans _ tail, visited⟩


theorem TapeBank.RegionRun.compile {data : InputData I A} {bits : BitString} {r : ℕ}
    {source : BankConfiguration O Q S k} {result : Outcome O}
    (run : B.RegionRun data bits r source result)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (ready : BankReady B source negative start) (region : (bankMachine B).InRegion r start) :
    ∃ ticks finish, (bankMachine B).Steps data bits start ticks finish ∧
      (bankMachine B).observe data bits finish = .halted result ∧ (bankMachine B).InRegion r finish := by
  obtain ⟨ticks, terminal, path, halt⟩ := run
  obtain ⟨cost, middle, sides, related, prefixPath, visited⟩ := path.compile B negative start ready region
  have table : B.instruction data terminal = .accept ∧ result = .accepted terminal.output ∨
      B.instruction data terminal = .reject ∧ result = .rejected ∨
      ∃ no yes, B.instruction data terminal = .readRandom no yes ∧ bits[terminal.randomHead]? = none ∧
        result = .exhausted := by
    cases halt with
    | accept c table => exact Or.inl ⟨table, rfl⟩
    | reject c table => exact Or.inr (Or.inl ⟨table, rfl⟩)
    | exhausted c no yes table absent => exact Or.inr (Or.inr ⟨no, yes, table, absent, rfl⟩)
  obtain ⟨finish, suffixPath, observed, region⟩ := bank_terminal_inRegion B data bits r terminal sides middle
    related (path.end_bound B) visited result table
  exact ⟨_, finish, prefixPath.trans _ suffixPath, observed, region⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank
