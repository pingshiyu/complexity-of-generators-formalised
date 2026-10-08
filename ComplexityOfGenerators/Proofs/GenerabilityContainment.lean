import ComplexityOfGenerators.Proofs.RecognitionSearch
import ComplexityOfGenerators.Simulation.WordInput

/-!
# The generator-to-recognizer half of Theorem 3.1

The finite-control input adapter removes the last encoding hypothesis from the
seed-search construction. The resulting recognizer reads ordinary words in
the original alphabet and uses the existing native machine model throughout.
-/

namespace ComplexityOfGenerators

open Simulation Encodable

variable {α : Type} [Fintype α] [Primcodable α]

/-- Mathlib's recursively enumerable word predicates have native recognizers
on the original alphabet, without totality or a resource bound. -/
theorem rePred_native_RE {L : Language α} (recursive : REPred (fun word => word ∈ L)) : L ∈ RE α := by
  let f : ℕ →. ℕ := fun code =>
    (decode (α := List α) code : Part (List α)).bind fun word =>
      (Part.assert (word ∈ L) (fun _ => Part.some ())).map (fun _ => 0)
  have membership : Partrec (fun word : List α =>
      (Part.assert (word ∈ L) (fun _ => Part.some ())).map (fun _ => (0 : ℕ))) :=
    recursive.map (Computable.const 0).to₂
  have codeRecursive : Partrec f :=
    (@Computable.decode (List α) _).ofOption.bind (membership.comp Computable.snd).to₂
  obtain ⟨native, deterministic, accepts⟩ := native_recognizer_of_partrec_words (I := α) codeRecursive
  refine ⟨native, deterministic, ?_⟩
  intro word
  rw [accepts word []]
  simp [f, Part.assert, Part.some]

/-- Exact agreement of recursive enumerability in Mathlib and in the paper's
native finite-control model. Neither side is redefined to obtain the equality. -/
theorem native_RE_iff_rePred (L : Language α) : L ∈ RE α ↔ REPred (fun word => word ∈ L) :=
  ⟨native_RE_rePred, rePred_native_RE⟩

/-- Completed containment in Theorem 3.1: every generator language has a
deterministic native recognizer reading the original word alphabet. -/
theorem gen_subset_re (α : Type) [Fintype α] : GEN α ⊆ RE α := by
  let : Primcodable α := Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)
  intro L generated
  exact rePred_native_RE (native_GEN_rePred generated)

end ComplexityOfGenerators
