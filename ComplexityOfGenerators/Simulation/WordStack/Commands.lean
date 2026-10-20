import ComplexityOfGenerators.Simulation.WordStack.Combinators

/-! A structured language of primitive stack commands. Branches inspect only
one stack symbol and the unary-index symbol. Compilation yields finite control,
including for loops; the execution relation charges all control transfers. -/

namespace ComplexityOfGenerators.Simulation.WordStack

abbrev Observation (S : Type) := Option S × Option Unit

def observe {S O : Type} {k : ℕ} (n : ℕ) (m : Memory S O k) (j : Fin k) : Observation S :=
  ((m.store j).head?, if m.indexHead < n then some () else none)

inductive Command (S O : Type) (k : ℕ)
  | skip
  | act (stack : Fin k) (action : Action S) (index : Move) (emit : Option O)
  | branch (stack : Fin k) (next : Observation S → Command S O k)
  | random (no yes : Command S O k)
  | seq (first second : Command S O k)
  | loop (stack : Fin k) (test : Observation S → Bool) (body : Command S O k)
  | drain

namespace Command

variable {S O : Type} {k : ℕ}

def Control : Command S O k → Type
  | .skip | .drain => Unit
  | .act .. => Bool
  | .branch _ next => Option ((o : Observation S) × Control (next o))
  | .random no yes => Option ((b : Bool) × match b with | false => Control no | true => Control yes)
  | .seq first second => Control first ⊕ Control second
  | .loop _ _ body => Option (Control body)

noncomputable instance controlFintype [Fintype S] : (c : Command S O k) → Fintype c.Control
  | .skip | .drain => inferInstanceAs (Fintype Unit)
  | .act .. => inferInstanceAs (Fintype Bool)
  | .branch _ next => by
    letI := fun o : Observation S => controlFintype (next o)
    exact inferInstanceAs (Fintype (Option ((o : Observation S) × Control (next o))))
  | .random no yes => by
    letI : (b : Bool) → Fintype (match b with | false => Control no | true => Control yes) :=
      fun b => match b with | false => controlFintype no | true => controlFintype yes
    exact inferInstanceAs (Fintype (Option ((b : Bool) × match b with | false => Control no | true => Control yes)))
  | .seq first second => by
    letI := controlFintype first
    letI := controlFintype second
    exact inferInstanceAs (Fintype (Control first ⊕ Control second))
  | .loop _ _ body => by
    letI := controlFintype body
    exact inferInstanceAs (Fintype (Option (Control body)))

def program (idle : Fin k) : (c : Command S O k) → Program c.Control S O k
  | .skip => Program.skip idle
  | .act j action index emit => Program.atom j action index emit
  | .branch j next => Program.branch j (fun cell index => (cell, index)) (fun o => program idle (next o))
  | .random no yes => Program.randomChoice idle
      (fun b => match b with | false => program idle no | true => program idle yes)
  | .seq first second => (program idle first).sequence (program idle second)
  | .loop j test body => (program idle body).loop j (fun cell index => test (cell, index))
  | .drain => Program.drain idle

inductive Runs (n : ℕ) (bits : BitString) :
    Command S O k → Memory S O k → ℕ → Result S O k → Prop
  | skip (m) : Runs n bits .skip m 0 (.done m)
  | act (m) (j action index emit) :
      Runs n bits (.act j action index emit) m 1 (.done (Program.changeMemory j n action index emit m))
  | branch (m) (j) (next : Observation S → Command S O k) (t result)
      (run : Runs n bits (next (observe n m j)) m t result) :
      Runs n bits (.branch j next) m (1 + t) result
  | random_absent (m) (no yes) (absent : bits[m.randomHead]? = none) :
      Runs n bits (.random no yes) m 0 .exhausted
  | random (m) (no yes) (bit : Bool) (t result) (lookup : bits[m.randomHead]? = some bit)
      (run : Runs n bits (if bit then yes else no) (Program.readBit m) t result) :
      Runs n bits (.random no yes) m (1 + t) result
  | seq_absent (m) (first second) (t) (run : Runs n bits first m t .exhausted) :
      Runs n bits (.seq first second) m t .exhausted
  | seq (m middle) (first second) (s t result)
      (left : Runs n bits first m s (.done middle)) (right : Runs n bits second middle t result) :
      Runs n bits (.seq first second) m (s + 1 + t) result
  | loop_stop (m) (j test body) (stop : test (observe n m j) = false) :
      Runs n bits (.loop j test body) m 0 (.done m)
  | loop_absent (m) (j test body) (t) (again : test (observe n m j) = true)
      (run : Runs n bits body m t .exhausted) :
      Runs n bits (.loop j test body) m (1 + t) .exhausted
  | loop (m middle) (j test body) (s t result) (again : test (observe n m j) = true)
      (run : Runs n bits body m s (.done middle)) (rest : Runs n bits (.loop j test body) middle t result) :
      Runs n bits (.loop j test body) m (1 + s + 1 + t) result
  | drain (m) : Runs n bits .drain m (bits.length - m.randomHead) .exhausted

theorem Runs.compiled (idle : Fin k) {n : ℕ} {bits : BitString} {c : Command S O k}
    {m : Memory S O k} {t : ℕ} {result : Result S O k} (run : c.Runs n bits m t result)
    (bounded : m.indexHead ≤ n) : (c.program idle).Evaluates n bits m t result := by
  induction run with
  | skip m => exact Program.skip_returns idle n bits m
  | act m j action index emit => exact Program.atom_returns j action index emit n bits m
  | branch m j next t result run ih =>
    exact Program.branch_evaluates j _ _ bounded (ih bounded)
  | random_absent m no yes absent => exact Program.randomChoice_exhausted idle _ m absent
  | random m no yes bit t result lookup run ih =>
    apply Program.randomChoice_evaluates idle _ bit lookup
    cases bit <;> exact ih bounded
  | seq_absent m first second t run ih =>
    exact (first.program idle).sequence_exhausted (second.program idle) (ih bounded)
  | seq m middle first second s t result left right ihLeft ihRight =>
    have runLeft := ihLeft bounded
    exact (first.program idle).sequence_return (second.program idle) bounded runLeft
      (ihRight (Program.Returns.index_le _ runLeft bounded))
  | loop_stop m j test body stop => exact (body.program idle).loop_stop j _ m stop
  | loop_absent m j test body t again run ih =>
    exact (body.program idle).loop_exhausted j _ bounded again (ih bounded)
  | loop m middle j test body s t result again run rest ihBody ihRest =>
    have runBody := ihBody bounded
    exact (body.program idle).loop_return j _ bounded again runBody
      (ihRest (Program.Returns.index_le _ runBody bounded))
  | drain m => exact Program.drain_evaluates idle n bits m

theorem Runs.index_le (idle : Fin k) {n : ℕ} {bits : BitString} {c : Command S O k}
    {m finish : Memory S O k} {t : ℕ} (run : c.Runs n bits m t (.done finish))
    (bounded : m.indexHead ≤ n) : finish.indexHead ≤ n :=
  Program.Returns.index_le _ (run.compiled idle bounded) bounded

end Command
end ComplexityOfGenerators.Simulation.WordStack
