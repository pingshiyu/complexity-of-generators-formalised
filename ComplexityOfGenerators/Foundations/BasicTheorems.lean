import ComplexityOfGenerators.Foundations.Classical
import Complexitylib.Classes.Containments.NPSPACESubsetPSPACE
import Complexitylib.Classes.Containments.NLSubsetP
import Complexitylib.SAT.CookLevin.Corollaries

/-!
# Classical theorems used by the paper

All results here reuse proved Complexitylib declarations. In particular, neither
Cook–Levin nor Savitch's theorem is asserted as an axiom or a `sorry`. The Savitch
API supplies class equality, which is sufficient for the unrelativised Theorem
6.1; it does not supply the oracle version or an extracted quantitative `s²`
bound for this project's read-once generator model.
-/

namespace ComplexityOfGenerators.Standard

theorem p_subset_np : P ⊆ NP := Complexity.P_subset_NP

theorem p_subset_pspace : P ⊆ PSPACE := Complexity.P_subset_PSPACE

theorem p_closed_under_complement {K : Complexity.Language} (h : K ∈ P) : Kᶜ ∈ P :=
  Complexity.P_compl h

theorem deterministic_time_subset_space (t : ℕ → ℕ) : DTIME t ⊆ DSPACE t :=
  Complexity.DTIME_subset_DSPACE t

/-- Savitch, in exactly the polynomial-space form needed by Theorem 6.1. -/
theorem savitch : NPSPACE ⊆ PSPACE := Complexity.NPSPACE_subset_PSPACE

theorem pspace_eq_npspace : PSPACE = NPSPACE := Complexity.PSPACE_eq_NPSPACE

theorem nl_subset_p : NL ⊆ P := Complexity.NL_subset_P

/-- Complexitylib's CNF encoding and SAT language, not a new syntax for SAT. -/
abbrev SAT := Complexity.SAT.language

abbrev UNSAT : Complexity.Language := SATᶜ

theorem cook_levin : NPComplete SAT := Complexity.SAT.NPComplete_language

theorem sat_mem_np : SAT ∈ NP := cook_levin.1

theorem unsat_co_np_complete : coNPComplete UNSAT :=
  Complexity.SAT.coNPComplete_compl_language

/-- The collapse used in the complement clause of Theorem 7.2. -/
theorem unsat_mem_np_iff : UNSAT ∈ NP ↔ NP = coNP := by
  change SAT ∈ coNP ↔ NP = coNP
  exact Complexity.SAT.language_mem_coNP_iff_NP_eq_coNP

theorem unsat_not_mem_np (h : NP ≠ coNP) : UNSAT ∉ NP :=
  fun member => h (unsat_mem_np_iff.mp member)

theorem karp_reduction_trans {A B C : Complexity.Language}
    (h₁ : KarpReduction A B) (h₂ : KarpReduction B C) : KarpReduction A C :=
  h₁.trans h₂

theorem karp_reduction_complement {A B : Complexity.Language}
    (h : KarpReduction A B) : KarpReduction Aᶜ Bᶜ := h.compl

end ComplexityOfGenerators.Standard
