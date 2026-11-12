import ComplexityOfGenerators.Examples.SATInversion
import Mathlib.Data.Nat.Log

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

def width (d : ℕ) : ℕ := if d = 0 then 0 else 1

theorem width_positive (d : ℕ) : 0 < width d ↔ 0 < d := by
  unfold width
  split <;> omega

theorem rank_encoding_bound {M d : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) : d ≤ (f.encode M d).length := by
  rw [f.encode_length bound valid]
  omega

theorem width_encoding_log_bound {M d : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) : width d ≤ Nat.log 2 (f.encode M d).length := by
  have size : 2 ≤ (f.encode M d).length := by
    rw [f.encode_length bound valid]
    omega
  have logarithm : 1 ≤ Nat.log 2 (f.encode M d).length :=
    Nat.le_log_of_pow_le (by decide) (by simpa using size)
  unfold width
  split <;> omega

theorem satisfiable_zero_iff (f : Formula) :
    Satisfiable 0 f ↔ f.eval (fun _ => false) = true := by
  constructor
  · rintro ⟨c, hc⟩
    have equal : c = [] := List.length_eq_zero_iff.mp hc.1
    simpa [equal, assignment] using hc.2
  · intro h
    exact ⟨[], rfl, h⟩

/-- The paper's repair of the all-false clause retains every already-true
constant vector, so it has full support on true vectors of the given length. -/
def forceTrue (bits : List Bool) : List Bool :=
  if bits.any id then bits else true :: bits.tail

theorem forceTrue_length (bits : List Bool) (nonempty : bits ≠ []) :
    (forceTrue bits).length = bits.length := by
  cases bits with
  | nil => contradiction
  | cons b rest => unfold forceTrue; split_ifs <;> rfl

theorem forceTrue_true (bits : List Bool) : (forceTrue bits).any id = true := by
  unfold forceTrue
  split_ifs with truth
  · exact truth
  · simp

theorem forceTrue_fixed (bits : List Bool) (truth : bits.any id = true) :
    forceTrue bits = bits := by simp [forceTrue, truth]

theorem forceTrue_image (n : ℕ) (positive : 0 < n) :
    {out | ∃ bits : List Bool, bits.length = n ∧ forceTrue bits = out} =
      {out | out.length = n ∧ out.any id = true} := by
  ext out
  constructor
  · rintro ⟨bits, length, rfl⟩
    have nonempty : bits ≠ [] := by intro empty; simp [empty] at length; omega
    exact ⟨(forceTrue_length bits nonempty).trans length, forceTrue_true bits⟩
  · rintro ⟨length, truth⟩
    exact ⟨out, length, forceTrue_fixed out truth⟩

end ComplexityOfGenerators.Examples.PaddedCNF
