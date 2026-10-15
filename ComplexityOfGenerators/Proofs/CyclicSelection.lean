import ComplexityOfGenerators.Proofs.GeometricSampling
import Mathlib.Data.List.GetD

/-!
# Almost-sure selection during cyclic enumeration

Appendix A.17 repeatedly enumerates accepted words, offering each one with
probability one half. At the level of accepted candidates, a true random bit
continues to the next candidate and a false bit selects the current one.

This module proves the support and probability facts for that protocol. The
list of accepted candidates is a semantic specification, not a proposed work-
tape representation: a polynomial-space implementation must enumerate and
check candidates while reusing workspace, rather than materializing this list.
-/

namespace ComplexityOfGenerators

/-- The cyclic position advances only when a candidate is declined. Empty
candidate lists and exhausted finite random tapes produce no output. -/
def cyclicSelection {α : Type} (candidates : List α) : ℕ → BitString → Option α
  | _, [] => none
  | position, false :: _ => candidates[position % candidates.length]?
  | position, true :: bits => cyclicSelection candidates (position + 1) bits

theorem cyclicSelection_empty {α : Type} (position : ℕ) (bits : BitString) :
    cyclicSelection ([] : List α) position bits = none := by
  induction bits generalizing position with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [cyclicSelection, ih]

theorem cyclicSelection_sound {α : Type} (candidates : List α) (position : ℕ)
    (bits : BitString) (value : α) (selected : cyclicSelection candidates position bits = some value) :
    value ∈ candidates := by
  induction bits generalizing position with
  | nil => cases selected
  | cons bit bits ih =>
      cases bit with
      | false => exact List.mem_of_getElem? selected
      | true => exact ih (position + 1) selected

theorem cyclicSelection_skip {α : Type} (candidates : List α) (position skipped : ℕ)
    (tail : BitString) :
    cyclicSelection candidates position (List.replicate skipped true ++ false :: tail) =
      candidates[(position + skipped) % candidates.length]? := by
  induction skipped generalizing position with
  | zero => rfl
  | succ skipped ih =>
      simp only [List.replicate_succ, List.cons_append, cyclicSelection, ih]
      congr 2
      omega

/-- Every listed candidate is selected by some nonempty finite seed, even when
the selected candidate itself is an empty word. -/
theorem cyclicSelection_complete {α : Type} (candidates : List α) (value : α)
    (member : value ∈ candidates) :
    ∃ bits : BitString, bits ≠ [] ∧ cyclicSelection candidates 0 bits = some value := by
  obtain ⟨i, bound, same⟩ := List.getElem_of_mem member
  refine ⟨List.replicate i true ++ [false], by simp, ?_⟩
  rw [cyclicSelection_skip candidates 0 i []]
  simpa [Nat.mod_eq_of_lt bound] using List.getElem?_eq_some_iff.mpr ⟨bound, same⟩

/-- Any stop bit in a finite tape guarantees selection from a nonempty list. -/
theorem cyclicSelection_some_of_stop {α : Type} (candidates : List α)
    (nonempty : candidates ≠ []) (position : ℕ) (bits : BitString)
    (stop : false ∈ bits) : ∃ value, cyclicSelection candidates position bits = some value := by
  induction bits generalizing position with
  | nil => simp at stop
  | cons bit bits ih =>
      cases bit with
      | false =>
          have positive : 0 < candidates.length := List.length_pos_iff.mpr nonempty
          exact ⟨candidates[position % candidates.length]'(Nat.mod_lt _ positive),
            List.getElem?_eq_getElem (Nat.mod_lt _ positive)⟩
      | true =>
          exact ih (position + 1) (by simpa using stop)

/-- Selection is stable under extending the random tape. -/
theorem cyclicSelection_append {α : Type} (candidates : List α) (position : ℕ)
    (bits tail : BitString) (value : α)
    (selected : cyclicSelection candidates position bits = some value) :
    cyclicSelection candidates position (bits ++ tail) = some value := by
  induction bits generalizing position with
  | nil => cases selected
  | cons bit bits ih =>
      cases bit with
      | false => exact selected
      | true => exact ih (position + 1) selected

def cyclicSelectionStreams {α : Type} (candidates : List α) : Set BitStream :=
  {stream | ∃ bits value, stream ∈ cylinder bits ∧ cyclicSelection candidates 0 bits = some value}

theorem cyclicSelectionStreams_empty {α : Type} :
    cyclicSelectionStreams ([] : List α) = ∅ := by
  ext stream
  simp [cyclicSelectionStreams, cyclicSelection_empty]

/-- Cyclic enumeration accepts almost every fair tape whenever an accepted
candidate exists. This uses the existing fair-coin geometric-sampling lemma;
no independence assumption about machine running times is needed. -/
theorem cyclicSelection_probability_one {α : Type} (candidates : List α)
    (nonempty : candidates ≠ []) : fairCoinMeasure (cyclicSelectionStreams candidates) = 1 := by
  have accepted : ∀ᵐ stream ∂fairCoinMeasure, stream ∈ cyclicSelectionStreams candidates := by
    filter_upwards [fairCoin_ae_stop_after_every_offset] with stream stops
    obtain ⟨n, _, stop⟩ := stops 0
    have present : false ∈ streamPrefix stream (n + 1) := by
      have lookup : (streamPrefix stream (n + 1))[n]? = some false := by
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by simp, ?_⟩
        simpa only [streamPrefix, List.getElem_ofFn] using stop
      exact List.mem_of_getElem? lookup
    obtain ⟨value, selected⟩ := cyclicSelection_some_of_stop candidates nonempty 0
      (streamPrefix stream (n + 1)) present
    exact ⟨streamPrefix stream (n + 1), value, stream_mem_prefix_cylinder _ _, selected⟩
  exact (MeasureTheory.measure_congr
    (Filter.eventuallyEqSet_univ.mpr accepted)).trans MeasureTheory.measure_univ

end ComplexityOfGenerators
