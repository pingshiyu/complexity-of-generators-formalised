import ComplexityOfGenerators.Foundations.TrialBounds

/-!
# Selecting from finitely many bounded trials

Each entry receives a fresh block of `budget` bits and one selection bit.
Failed entries are skipped; declining every offer still returns a successful
entry if one exists. The construction both preserves full support and succeeds
on every full seed whenever any entry always succeeds on full seeds.

This is an executable finite-seed algorithm; its source calls and native
implementation are accounted for separately.
-/

namespace ComplexityOfGenerators.BoundedTrialChoice

variable {α : Type}

def prefer : Option α → Option α → Option α
  | none, other => other
  | some x, _ => some x

@[simp] theorem prefer_none_iff (a b : Option α) : prefer a b = none ↔ a = none ∧ b = none := by
  cases a <;> simp [prefer]

theorem prefer_some {a b : Option α} {x : α} (h : prefer a b = some x) :
    a = some x ∨ b = some x := by
  cases a <;> simp_all [prefer]

def run (budget : ℕ) : List (BitString → Option α) → BitString → Option α
  | [], _ => none
  | trial :: rest, bits =>
    let first := trial (bits.take budget)
    let later := run budget rest (bits.drop (budget + 1))
    if bits[budget]? = some true then prefer first later else prefer later first

/-- Every list entry gets a source seed and a selection bit, including failed
entries. Thus the input partition does not depend on source outcomes. -/
def seedLength (budget : ℕ) (trials : List (BitString → Option α)) : ℕ :=
  trials.length * (budget + 1)

theorem split_lengths (budget : ℕ) (trial : BitString → Option α)
    (rest : List (BitString → Option α)) {bits : BitString}
    (length : bits.length = seedLength budget (trial :: rest)) :
    (bits.take budget).length = budget ∧
      (bits.drop (budget + 1)).length = seedLength budget rest := by
  simp only [seedLength, List.length_cons, Nat.add_mul] at length
  simp only [List.length_take, List.length_drop, seedLength]
  constructor <;> omega

theorem run_block (budget : ℕ) (trial : BitString → Option α)
    (rest : List (BitString → Option α)) (seed : BitString) (bit : Bool) (tail : BitString)
    (length : seed.length = budget) :
    run budget (trial :: rest) (seed ++ bit :: tail) =
      if bit then prefer (trial seed) (run budget rest tail)
      else prefer (run budget rest tail) (trial seed) := by
  subst budget
  simp [run, List.drop_append, List.drop_eq_nil_of_le (Nat.le_succ seed.length)]

/-- Unused random bits do not change a completed full trial. -/
theorem append_unused {budget : ℕ} {trials : List (BitString → Option α)}
    {bits : BitString} (length : bits.length = seedLength budget trials) (extra : BitString) :
    run budget trials (bits ++ extra) = run budget trials bits := by
  induction trials generalizing bits with
  | nil => rfl
  | cons trial rest ih =>
    obtain ⟨firstLength, restLength⟩ := split_lengths budget trial rest length
    have enough : budget + 1 ≤ bits.length := by
      simp only [seedLength, List.length_cons, Nat.add_mul] at length
      omega
    have take : (bits ++ extra).take budget = bits.take budget :=
      List.take_append_of_le_length (by omega)
    have drop : (bits ++ extra).drop (budget + 1) = bits.drop (budget + 1) ++ extra :=
      List.drop_append_of_le_length enough
    simp only [run, take, drop, List.getElem?_append_left (by omega : budget < bits.length),
      ih restLength]

theorem sound {budget : ℕ} {trials : List (BitString → Option α)} {bits : BitString} {x : α}
    (length : bits.length = seedLength budget trials) (output : run budget trials bits = some x) :
    ∃ trial ∈ trials, ∃ seed, seed.length = budget ∧ trial seed = some x := by
  induction trials generalizing bits with
  | nil => simp [run] at output
  | cons trial rest ih =>
    obtain ⟨firstLength, restLength⟩ := split_lengths budget trial rest length
    have cases : trial (bits.take budget) = some x ∨
        run budget rest (bits.drop (budget + 1)) = some x := by
      unfold run at output
      split_ifs at output
      · exact prefer_some output
      · exact (prefer_some output).symm
    rcases cases with first | later
    · exact ⟨trial, by simp, bits.take budget, firstLength, first⟩
    · obtain ⟨f, member, seed, size, result⟩ := ih restLength later
      exact ⟨f, by simp [member], seed, size, result⟩

theorem complete {budget : ℕ} {trials : List (BitString → Option α)} {trial : BitString → Option α}
    {x : α} (member : trial ∈ trials) {seed : BitString}
    (length : seed.length = budget) (output : trial seed = some x) :
    ∃ bits, bits.length = seedLength budget trials ∧ run budget trials bits = some x := by
  induction trials with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · let tail : BitString := List.replicate (seedLength budget rest) false
      refine ⟨seed ++ true :: tail, ?_, ?_⟩
      · simp [tail, length, seedLength, Nat.add_mul]; omega
      · rw [run_block budget trial rest seed true tail length]
        simp [output, prefer]
    · obtain ⟨tail, tailLength, result⟩ := ih member
      let front : BitString := List.replicate budget false
      refine ⟨front ++ false :: tail, ?_, ?_⟩
      · simp [front, tailLength, seedLength, Nat.add_mul]; omega
      · rw [run_block budget first rest front false tail (by simp [front])]
        simp [result, prefer]

theorem total_of_entry {budget : ℕ} {trials : List (BitString → Option α)}
    {trial : BitString → Option α} (member : trial ∈ trials)
    (productive : ∀ seed, seed.length = budget → ∃ x, trial seed = some x)
    {bits : BitString} (length : bits.length = seedLength budget trials) :
    ∃ x, run budget trials bits = some x := by
  induction trials generalizing bits with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨firstLength, restLength⟩ := split_lengths budget first rest length
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨x, hx⟩ := productive _ firstLength
      simp only [run, hx]
      split_ifs <;> cases run budget rest (bits.drop (budget + 1)) <;> simp [prefer]
    · obtain ⟨x, hx⟩ := ih member restLength
      simp only [run, hx]
      split_ifs <;> cases first (bits.take budget) <;> simp [prefer]

/-- If each individual full trial detects a fixed emptiness predicate, the
combined trial detects that all entries are empty. -/
theorem none_iff {budget : ℕ} {trials : List (BitString → Option α)}
    (empty : (BitString → Option α) → Prop)
    (contract : ∀ trial ∈ trials, ∀ seed, seed.length = budget →
      (trial seed = none ↔ empty trial)) {bits : BitString}
    (length : bits.length = seedLength budget trials) :
    run budget trials bits = none ↔ ∀ trial ∈ trials, empty trial := by
  induction trials generalizing bits with
  | nil => simp [run]
  | cons trial rest ih =>
    obtain ⟨firstLength, restLength⟩ := split_lengths budget trial rest length
    have first := contract trial (by simp) _ firstLength
    have later := ih (fun f member => contract f (by simp [member])) restLength
    simp only [run]
    split_ifs <;> simp only [prefer_none_iff, first, later, List.forall_mem_cons]
    exact and_comm

end ComplexityOfGenerators.BoundedTrialChoice
