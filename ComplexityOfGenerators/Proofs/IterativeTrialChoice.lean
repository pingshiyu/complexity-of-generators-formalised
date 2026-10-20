import ComplexityOfGenerators.Proofs.BoundedTrialChoice

/-! A forward scan implements the bounded trial selector. A successful offer
locks the result; before that, each success becomes the fallback. -/

namespace ComplexityOfGenerators.BoundedTrialChoice

variable {α : Type}

structure Selection (α : Type) where
  candidate : Option α
  locked : Bool

def Selection.offer (s : Selection α) (result : Option α) (coin : Bool) : Selection α :=
  if s.locked then s else match result with
    | none => s
    | some a => ⟨some a, coin⟩

def scan (budget : ℕ) : List (BitString → Option α) → BitString → Selection α → Selection α
  | [], _, s => s
  | trial :: rest, bits, s =>
    scan budget rest (bits.drop (budget + 1))
      (s.offer (trial (bits.take budget)) (bits[budget]? == some true))

theorem scan_result (budget : ℕ) (trials : List (BitString → Option α)) (bits : BitString) (s : Selection α) :
    (scan budget trials bits s).candidate =
      if s.locked then s.candidate else prefer (run budget trials bits) s.candidate := by
  induction trials generalizing bits s with
  | nil =>
    cases s with
    | mk candidate locked => cases locked <;> simp [scan, run, prefer]
  | cons trial rest ih =>
    rw [scan, ih]
    cases s with
    | mk candidate locked =>
      cases locked with
      | true => simp [Selection.offer]
      | false =>
        cases result : trial (bits.take budget)
        all_goals
          cases coin : bits[budget]? with
          | none => cases tail : run budget rest (bits.drop (budget + 1)) <;>
              simp [Selection.offer, run, result, coin, prefer, tail]
          | some bit => cases bit <;> cases tail : run budget rest (bits.drop (budget + 1)) <;>
              simp [Selection.offer, run, result, coin, prefer, tail]

@[simp] theorem scan_empty (budget : ℕ) (trials : List (BitString → Option α)) (bits : BitString) :
    (scan budget trials bits ⟨none, false⟩).candidate = run budget trials bits := by
  rw [scan_result]
  cases run budget trials bits <;> rfl

end ComplexityOfGenerators.BoundedTrialChoice
