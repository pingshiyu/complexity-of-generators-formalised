import ComplexityOfGenerators.Simulation.StarPaths.Correctness
import ComplexityOfGenerators.Simulation.StarPaths.Basic

/-! The DP archive stores one positive-composition witness per smaller sum.
Its unary payload is quadratic in the target, including entry markers. -/
namespace ComplexityOfGenerators.Simulation.StarPaths
set_option backward.isDefEq.respectTransparency false

@[simp] theorem entry_length (value : Option Parts) :
    (entry value).length = (held value).length+1 := by
  cases value <;> simp [entry, held]

theorem encoded_length_le (entries : Table) (bound : ℕ)
    (bounded : ∀ value ∈ entries, (held value).length ≤ bound) :
    (encoded entries).length ≤ entries.length*(bound+1) := by
  induction entries with
  | nil => simp [encoded]
  | cons value rest ih =>
    have first := bounded value (by simp)
    have tail : ∀ prior ∈ rest, (held prior).length ≤ bound :=
      fun prior member => bounded prior (by simp [member])
    have remaining := ih tail
    dsimp only [encoded] at remaining
    simp only [encoded, List.flatMap_cons, List.length_append, entry_length, List.length_cons]
    nlinarith

theorem archive_held_length (flags : List Bool) (n : ℕ) (value : Option Parts)
    (member : value ∈ archive flags n) : (held value).length ≤ 2*n := by
  cases value with
  | none => simp [held]
  | some parts =>
    obtain ⟨k, inside, cell⟩ := List.mem_iff_getElem.mp member
    have found : (archive flags n)[k]? = some (some parts) := by
      rw [List.getElem?_eq_getElem inside, cell]
    have sound := archive_sound flags n k parts found
    exact (valid_payload_bound flags (n-k) parts sound).trans (Nat.mul_le_mul_left 2 (Nat.sub_le n k))

theorem archive_encoded_length (flags : List Bool) (n : ℕ) :
    (encoded (archive flags n)).length ≤ (n+1)*(2*n+1) := by
  simpa only [archive_length] using
    encoded_length_le (archive flags n) (2*n) (archive_held_length flags n)

end ComplexityOfGenerators.Simulation.StarPaths
