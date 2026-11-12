import ComplexityOfGenerators.Examples.SATNative.VerifierBounds
import ComplexityOfGenerators.Examples.SATBaseDefaults
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] NativeEvaluation.verifier

abbrev Store := Local.Store Symbol 35

def verifierSlots : Fin 32 ↪ Fin 35 :=
  ⟨fun j => ⟨j.val, by omega⟩, by intro a b same; exact Fin.ext (congrArg (fun j : Fin 35 => j.val) same)⟩

noncomputable def check : Routine Symbol Symbol 35 :=
  (NativeEvaluation.verifier (O := Symbol)).rename verifierSlots

def verdict (s : Store) : Bool :=
  (s 2).isEmpty && !(s 17).head?.isSome && (s 6).head?.isSome

theorem check_here (s : Store) (j : Fin 32) :
    check.eval s (verifierSlots j) = (NativeEvaluation.verifier (O := Symbol)).eval (s ∘ verifierSlots) j :=
  Routine.rename_eval_here _ _ _ _

theorem check_verdict (s : Store) : verdict (check.eval s) = NativeEvaluation.verifies (s 2) (s 3) := by
  have word := check_here s 2
  have inside := check_here s 17
  have valid := check_here s 6
  change check.eval s 2 = _ at word
  change check.eval s 17 = _ at inside
  change check.eval s 6 = _ at valid
  unfold verdict
  rw [word, inside, valid]
  exact NativeEvaluation.verifier_decides (O := Symbol) (s ∘ verifierSlots)

theorem check_frame (s : Store) (j : Fin 35) (outside : 32 ≤ j.val) : check.eval s j = s j := by
  apply Routine.rename_eval_frame
  intro i equal
  have same := congrArg Fin.val equal
  change j.val = i.val at same
  have := i.isLt
  omega

theorem check_cost (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    check.cost s ≤ (NativeEvaluation.stepConstant + 400) * (budget + 2)^2 := by
  exact NativeEvaluation.verifier_cost (O := Symbol) _ budget (by intro j; exact sizes (verifierSlots j))

theorem empty_certificate_iff_bases (word : List Symbol) (n : ℕ) (length : word.length = n) :
    [] ∈ wordCertificates word ↔ word ∈ selfReduction.bases n := by
  change _ ↔ word ∈ selfReduction.ancestors n ∧ wordRank word = 0
  rw [ancestors_eq_slice]
  constructor
  · intro accepted
    exact ⟨⟨(word_mem_iff_certificates word).mpr ⟨[], accepted⟩, length⟩,
      (word_certificate_length word [] accepted).symm⟩
  · rintro ⟨⟨member, _⟩, rank⟩
    obtain ⟨certificate, good⟩ := (word_mem_iff_certificates word).mp member
    have size := word_certificate_length word certificate good
    have empty : certificate = [] := List.length_eq_zero_iff.mp (size.trans rank)
    simpa only [empty] using good

theorem verifies_iff_bases (word : List Symbol) (n : ℕ) (length : word.length = n) :
    NativeEvaluation.verifies word [] = true ↔ word ∈ selfReduction.bases n := by
  rw [NativeEvaluation.verifies_iff]
  exact empty_certificate_iff_bases word n length

end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
