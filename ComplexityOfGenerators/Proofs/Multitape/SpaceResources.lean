import ComplexityOfGenerators.MultitapeSpaceClasses
import ComplexityOfGenerators.Proofs.Multitape.ResourceOrder
import Mathlib.Data.Nat.Log

/-! Arithmetic for logarithmic preprocessing and finite-configuration clocks.
The actual simulations are proved separately; these lemmas only assemble their
charged work bounds in the shared eventual-multiplicative convention. -/
namespace ComplexityOfGenerators.Multitape

/-- A strict integral logarithmic lower bound also covers the physical binary
input-length counter, including its highest digit. -/
theorem clog_succ_le_of_log_lt {n bound : ℕ} (dominates : Nat.log 2 n<bound) :
    Nat.clog 2 (n+1)≤bound := by
  apply Nat.clog_le_of_le_pow
  have power := Nat.lt_pow_of_log_lt (by decide : 1<2) dominates
  omega

theorem ResourceOrder.logarithm {space : ℕ→ℕ} (dominates : ∀ n,Nat.log 2 n<space n) :
    ResourceOrder (fun n=>Nat.clog 2 (n+1)) space :=
  ⟨1,0,by decide,fun n _=>by simpa using clog_succ_le_of_log_lt (dominates n)⟩

theorem eventually_positive_of_logarithm {space : ℕ→ℕ} (dominates : ∀ n,Nat.log 2 n<space n) :
    ∃ threshold,∀ n,threshold≤n → 1≤space n :=
  ⟨0,fun n _=>by have positive:=dominates n;omega⟩

theorem ResourceOrder.mono {first second target : ℕ→ℕ} (bound : ResourceOrder second target)
    (pointwise : ∀ n,first n≤second n) : ResourceOrder first target := by
  obtain ⟨constant,threshold,positive,bounded⟩ := bound
  exact ⟨constant,threshold,positive,fun n large=>(pointwise n).trans (bounded n large)⟩

theorem ResourceOrder.logarithm_of_linear {space : ℕ→ℕ} (dominates : ∀ n,n≤space n) :
    ResourceOrder (fun n=>Nat.clog 2 (n+1)) space := by
  have power (n : ℕ) : n+1≤2^n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ];omega
  exact ⟨1,0,by decide,fun n _=>by simpa using (Nat.clog_le_of_le_pow (power n)).trans (dominates n)⟩

theorem eventually_positive_of_linear {space : ℕ→ℕ} (dominates : ∀ n,n≤space n) :
    ∃ threshold,∀ n,threshold≤n → 1≤space n := ⟨1,fun n positive=>positive.trans (dominates n)⟩

theorem ResourceOrder.with_logarithmic_setup_of_bounds {workspace space : ℕ→ℕ}
    (bounded : ResourceOrder workspace space) (logarithm : ResourceOrder (fun n=>Nat.clog 2 (n+1)) space)
    (positive : ∃ threshold,∀ n,threshold≤n → 1≤space n)
    (sourceScale logarithmScale offset : ℕ) :
    ResourceOrder (fun n=>sourceScale*workspace n+logarithmScale*Nat.clog 2 (n+1)+offset) space := by
  have first := bounded.affine positive sourceScale offset
  have second := logarithm.affine positive logarithmScale 0
  simpa only [Nat.add_zero,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.add second

/-- Every fixed affine combination of source work and binary setup remains
O(s) under the paper's logarithmic lower bound. -/
theorem ResourceOrder.with_logarithmic_setup {workspace space : ℕ→ℕ}
    (bounded : ResourceOrder workspace space) (dominates : ∀ n,Nat.log 2 n<space n)
    (sourceScale logarithmScale offset : ℕ) :
    ResourceOrder (fun n=>sourceScale*workspace n+logarithmScale*Nat.clog 2 (n+1)+offset) space := by
  have positive := eventually_positive_of_logarithm dominates
  have first := bounded.affine positive sourceScale offset
  have second := (ResourceOrder.logarithm dominates).affine positive logarithmScale 0
  simpa only [Nat.add_zero,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.add second

end ComplexityOfGenerators.Multitape
