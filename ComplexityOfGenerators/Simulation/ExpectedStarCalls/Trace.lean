import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Basic

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls

variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

structure Record (α : Type) where
  failures : ℕ
  word : List α

def Record.blocks (record : Record α) : ℕ := record.failures+1

def consumed : List ℕ → List (Record α) → ℕ
  | j::parts, record::records => record.blocks*P.seed j+consumed parts records
  | _, _ => 0

def blocks (records : List (Record α)) : ℕ := (records.map Record.blocks).sum

def words (records : List (Record α)) : List α := records.flatMap Record.word

/-- An exact finite successful prefix for each successive call, at its actual
fresh random head. A record counts failures before the successful block. -/
def Trace (bits : BitString) (offset : ℕ) : List ℕ → List (Record α) → Prop
  | [], [] => True
  | j::parts, record::records =>
      offset+record.blocks*P.seed j ≤ bits.length ∧
      (∀ k < record.failures,
        UnionGenerator.sourceValue P.machine P.clock j
          ((bits.drop (offset+k*P.seed j)).take (P.seed j)) = none) ∧
      UnionGenerator.sourceValue P.machine P.clock j
        ((bits.drop (offset+record.failures*P.seed j)).take (P.seed j)) = some record.word ∧
      Trace bits (offset+record.blocks*P.seed j) parts records
  | _, _ => False

theorem Trace.length_eq {bits : BitString} {offset : ℕ} {parts : List ℕ} {records : List (Record α)}
    (trace : Trace P bits offset parts records) : parts.length = records.length := by
  induction parts generalizing records offset with
  | nil => cases records <;> simp_all [Trace]
  | cons j parts ih =>
      cases records with
      | nil => exact False.elim trace
      | cons record records => exact congrArg Nat.succ (ih trace.2.2.2)

theorem blocks_ge_length (records : List (Record α)) : records.length ≤ blocks records := by
  induction records with
  | nil => simp [blocks]
  | cons record records ih =>
      simp only [blocks, List.map_cons, List.sum_cons, List.length_cons] at *
      unfold Record.blocks at *
      omega

end ComplexityOfGenerators.Simulation.ExpectedStarCalls
