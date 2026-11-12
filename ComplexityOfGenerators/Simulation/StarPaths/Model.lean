import ComplexityOfGenerators.Simulation.WordStack.TransferWhile

/-! A bounded dynamic program and cut-coin proposal for compositions whose
positive parts have been certified available. These definitions are the pure
semantics of the native routines in this directory. -/
namespace ComplexityOfGenerators.Simulation.StarPaths

set_option backward.isDefEq.respectTransparency false

inductive Symbol
  | unit | cut | absent | present | bitFalse | bitTrue
  deriving DecidableEq, Fintype

abbrev Parts := List ℕ
abbrev Table := List (Option Parts)

def payload (parts : Parts) : List Symbol :=
  parts.flatMap (fun j => Symbol.cut :: List.replicate j Symbol.unit)

def certified (flags : List Bool) (j : ℕ) : Prop :=
  0 < j ∧ (flags[j-1]?).getD false = true

def Valid (flags : List Bool) (n : ℕ) (parts : Parts) : Prop :=
  parts.sum = n ∧ ∀ j ∈ parts, certified flags j

def candidate (flag : Bool) (j : ℕ) (previous : Option Parts) : Option Parts :=
  if flag then previous.map (List.cons j) else none

def offer (current next : Option Parts) : Option Parts :=
  if current.isSome then current else next

/-- The archive is in decreasing sum order, so the first previous entry in
stage m concerns m-1, paired with source index 1. -/
def scan : List Bool → Table → ℕ → Option Parts → Option Parts
  | _, [], _, current => current
  | flags, previous :: rest, j, current =>
      scan flags.tail rest (j+1)
        (offer current (candidate ((flags[0]?).getD false) j previous))

def stage (flags : List Bool) (archive : Table) : Option Parts := scan flags archive 1 none

def archive (flags : List Bool) : ℕ → Table
  | 0 => [some []]
  | n+1 => let prior := archive flags n; stage flags prior :: prior

def fallback (flags : List Bool) (n : ℕ) : Option Parts := (archive flags n).head?.bind id

@[simp] theorem archive_length (flags : List Bool) (n : ℕ) : (archive flags n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [archive,ih]

@[simp] theorem fallback_zero (flags : List Bool) : fallback flags 0 = some [] := rfl
@[simp] theorem fallback_succ (flags : List Bool) (n : ℕ) : fallback flags (n+1) = stage flags (archive flags n) := rfl

@[simp] theorem offer_some (parts : Parts) (next : Option Parts) : offer (some parts) next = some parts := rfl
@[simp] theorem offer_none (next : Option Parts) : offer none next = next := rfl

@[simp] theorem scan_some (flags : List Bool) (entries : Table) (j : ℕ) (parts : Parts) :
    scan flags entries j (some parts) = some parts := by
  induction entries generalizing flags j with
  | nil => rfl
  | cons previous rest ih => simp only [scan,offer_some]; exact ih flags.tail (j+1)

/-- Every result comes from the initial candidate or one scanned table cell. -/
theorem scan_result (flags : List Bool) (entries : Table) (j : ℕ) (current : Option Parts) (parts : Parts)
    (result : scan flags entries j current = some parts) :
    current = some parts ∨ ∃ (k : ℕ) (previous : Parts), entries[k]? = some (some previous) ∧
      (flags[k]?).getD false = true ∧ parts = (j+k)::previous := by
  induction entries generalizing flags j current with
  | nil => exact Or.inl result
  | cons previous rest ih =>
      have next := ih flags.tail (j+1) (offer current (candidate ((flags[0]?).getD false) j previous)) result
      rcases next with immediate | ⟨k,prior,entry,flag,equal⟩
      · cases current with
        | some initial => exact Or.inl immediate
        | none =>
          cases available : (flags[0]?).getD false with
          | false => simp [candidate,available] at immediate
          | true =>
              cases previous with
              | none => simp [candidate,available] at immediate
              | some prior =>
                  have value : j::prior = parts := by simpa [candidate,available] using immediate
                  refine Or.inr ⟨0,prior,by simp,?_,?_⟩
                  · simpa using available
                  · simpa using value.symm
      · refine Or.inr ⟨k+1,prior,?_,?_,?_⟩
        · simpa using entry
        · simpa only [List.getElem?_tail] using flag
        · simpa only [Nat.add_assoc,Nat.add_comm 1 k] using equal

/-- A supplied initial result, or any available table cell, guarantees that
this first-witness scan returns a result. -/
theorem scan_isSome (flags : List Bool) (entries : Table) (j : ℕ) (current : Option Parts) :
    (scan flags entries j current).isSome = true ↔ current.isSome = true ∨
      ∃ (k : ℕ) (previous : Parts), entries[k]? = some (some previous) ∧ (flags[k]?).getD false = true := by
  constructor
  · intro present
    obtain ⟨parts,result⟩ := Option.isSome_iff_exists.mp present
    rcases scan_result flags entries j current parts result with immediate | ⟨k,prior,entry,flag,_⟩
    · exact Or.inl (by simp [immediate])
    · exact Or.inr ⟨k,prior,entry,flag⟩
  · intro witness
    cases current with
    | some parts => simp
    | none =>
      rcases witness with impossible | ⟨k,prior,entry,flag⟩
      · simp at impossible
      · induction entries generalizing flags j k with
        | nil => simp at entry
        | cons previous rest ih =>
          cases k with
          | zero =>
              have previousEq : previous = some prior := by simpa using entry
              have available : (flags[0]?).getD false = true := by simpa using flag
              simp only [scan,offer_none,candidate,available,ite_true,previousEq,Option.map_some,scan_some,Option.isSome_some]
          | succ k =>
              have cell : rest[k]? = some (some prior) := by simpa using entry
              have available : (flags.tail[k]?).getD false = true := by simpa only [List.getElem?_tail] using flag
              simp only [scan,offer_none]
              cases value : candidate ((flags[0]?).getD false) j previous with
              | some parts => simp
              | none => exact ih flags.tail (j+1) k cell available

end ComplexityOfGenerators.Simulation.StarPaths
