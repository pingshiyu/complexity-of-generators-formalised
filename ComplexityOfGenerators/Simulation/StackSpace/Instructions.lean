import ComplexityOfGenerators.Simulation.StackSpace.Program

/-! Exact execution of push, pop, peek and finite local control. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing


noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S Q V : Type} {k : ℕ} [Fintype Q]
variable (P : Q → Stmt S Q V k) (entry : Q) (initial : V) (answer : V → Bool)
variable (word : List S) (bits : BitString)

local notation "B" => bank P entry initial answer
local notation "C" => configuration P word.length
local notation "D" => decisionData word

theorem go (state next : State P) (stk : Fin (k + 1) → List S)
    (table : (B).instruction D (C state stk) = .step next none .stay .stay .stay .stay none) :
    (B).Steps D bits (C state stk) 1 (C next stk) := by
  have h := TransducerBank.TapeBank.Steps.go B D bits (C state stk) next
    (by rfl) (by simp [configuration, decisionData]) (by simp [configuration, decisionData])
    (by simpa only [configuration, stackTape_end] using table)
  exact h

theorem push (j : Fin (k + 1)) (f : V → S) (a : Stmt S Q V k)
    (ha : TM2.Stmt.push j f a ∈ statements P) (v : V) (stk : Fin (k + 1) → List S) :
    (B).Steps D bits (C (.exec ⟨.push j f a, ha⟩ v) stk) 1
      (C (.exec ⟨a, substatement_mem P ha (by classical simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v)
        (Function.update stk j (f v :: stk j))) := by
  classical
  have table : (B).instruction D (C (.exec ⟨.push j f a, ha⟩ v) stk) =
      .step (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ v)
        (some (f v)) .right .stay .stay .stay none := by
    simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected]
  have h := TransducerBank.TapeBank.Steps.single B D bits _ _ _ _ _ _ _ _ table
  convert h using 1
  apply TransducerBank.BankConfiguration.ext
  all_goals simp [TransducerBank.TapeBank.advance, configuration, bank, selected, Move.onInt, Move.onInput, decisionData]
  · funext i
    by_cases same : i = j <;> simp [same]
  · funext i
    by_cases same : i = j <;> simp [same, stackTape_cons]

def readConfiguration (P : Q → Stmt S Q V k) (inputLength : ℕ) (a : Node P) (v : V)
    (stk : Fin (k + 1) → List S) (j : Fin (k + 1)) : Config P :=
  {configuration P inputLength (.read a v) stk with
    head := Function.update (fun i => ((stk i).length : ℤ)) j ((stk j).length - 1)}

theorem begin_read (a : Node P) (v : V) (stk : Fin (k + 1) → List S) (j : Fin (k + 1))
    (sel : selected P (.exec a v) = j)
    (table : (B).instruction D (C (.exec a v) stk) = .step (.read a v) none .left .stay .stay .stay none) :
    (B).Steps D bits (C (.exec a v) stk) 1 (readConfiguration P word.length a v stk j) := by
  have h := TransducerBank.TapeBank.Steps.read B D bits (C (.exec a v) stk) (.read a v) .left j sel
    (by rfl) (by simp [configuration, decisionData]) (by simp [configuration, decisionData])
    (by simpa [configuration] using table)
  exact h

theorem pop (j : Fin (k + 1)) (f : V → Option S → V) (a : Stmt S Q V k)
    (ha : TM2.Stmt.pop j f a ∈ statements P) (v : V) (stk : Fin (k + 1) → List S) :
    ∃ t ≤ 2, (B).Steps D bits (C (.exec ⟨.pop j f a, ha⟩ v) stk) t
      (C (.exec ⟨a, substatement_mem P ha (by classical simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (stk j).head?))
        (Function.update stk j (stk j).tail)) := by
  classical
  cases hs : stk j with
  | nil =>
      have upd : Function.update stk j [] = stk := by
        rw [← hs]; exact Function.update_eq_self j stk
      simp only [List.tail_nil, upd]
      refine ⟨1, by omega, go P entry initial answer word bits _ _ stk ?_⟩
      simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected, hs]
  | cons s xs =>
      have nonempty : stk j ≠ [] := by simp [hs]
      let start := C (.exec ⟨.pop j f a, ha⟩ v) stk
      let middle := readConfiguration P word.length ⟨.pop j f a, ha⟩ v stk j
      have first : (B).Steps D bits start 1 middle := by
        apply begin_read P entry initial answer word bits _ _ _ j rfl
        simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected, nonempty]
      have table : (B).instruction D middle =
          .step (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (some s)))
            none .stay .stay .stay .stay none := by
        simp [middle, readConfiguration, TransducerBank.TapeBank.instruction, bank, transition, configuration,
          selected, hs, Nat.cast_add, Nat.cast_one]
      have second := TransducerBank.TapeBank.Steps.single B D bits middle _ _ _ _ _ _ _ table
      have finish : (B).advance D middle
          (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (some s)))
          none .stay .stay .stay .stay none =
          C (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (stk j).head?))
            (Function.update stk j (stk j).tail) := by
        apply TransducerBank.BankConfiguration.ext
        all_goals simp [TransducerBank.TapeBank.advance, middle, readConfiguration, configuration, bank, selected,
          Move.onInt, Move.onInput, decisionData, hs]
        · funext i
          by_cases same : i = j <;> simp [same]
        · funext i
          by_cases same : i = j
          · subst i; simp [stackTape_pop]
          · simp [same]
      rw [finish] at second
      exact ⟨2, le_rfl, by simpa [hs] using first.trans B second⟩

theorem peek (j : Fin (k + 1)) (f : V → Option S → V) (a : Stmt S Q V k)
    (ha : TM2.Stmt.peek j f a ∈ statements P) (v : V) (stk : Fin (k + 1) → List S) :
    ∃ t ≤ 2, (B).Steps D bits (C (.exec ⟨.peek j f a, ha⟩ v) stk) t
      (C (.exec ⟨a, substatement_mem P ha (by classical simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (stk j).head?)) stk) := by
  classical
  cases hs : stk j with
  | nil =>
      refine ⟨1, by omega, go P entry initial answer word bits _ _ stk ?_⟩
      simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected, hs]
  | cons s xs =>
      have nonempty : stk j ≠ [] := by simp [hs]
      let middle := readConfiguration P word.length ⟨.peek j f a, ha⟩ v stk j
      have first : (B).Steps D bits (C (.exec ⟨.peek j f a, ha⟩ v) stk) 1 middle := by
        apply begin_read P entry initial answer word bits _ _ _ j rfl
        simp [TransducerBank.TapeBank.instruction, bank, transition, configuration, selected, nonempty]
      have table : (B).instruction D middle =
          .step (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (some s)))
            (some s) .right .stay .stay .stay none := by
        simp [middle, readConfiguration, TransducerBank.TapeBank.instruction, bank, transition, configuration,
          selected, hs, Nat.cast_add, Nat.cast_one]
      have second := TransducerBank.TapeBank.Steps.read B D bits middle
        (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (some s))) .right j rfl
        (by rfl) (by simp [middle, readConfiguration, configuration, decisionData])
        (by simp [middle, readConfiguration, configuration, decisionData])
        (by simpa [middle, readConfiguration, configuration, hs] using table)
      have finish : {middle with
          state := .exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (some s))
          head := Function.update middle.head j (Move.right.onInt (middle.head j))} =
          C (.exec ⟨a, substatement_mem P ha (by simp [TM2.stmts₁, TM2.stmts₁_self])⟩ (f v (stk j).head?)) stk := by
        apply TransducerBank.BankConfiguration.ext
        all_goals simp [middle, readConfiguration, configuration, hs, Move.onInt]
      rw [finish] at second
      exact ⟨2, le_rfl, by simpa [hs] using first.trans B second⟩

end
end ComplexityOfGenerators.Simulation.StackSpace
