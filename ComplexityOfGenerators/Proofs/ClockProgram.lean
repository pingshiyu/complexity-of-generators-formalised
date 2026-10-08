import ComplexityOfGenerators.Proofs.ClockedSampling
import ComplexityOfGenerators.Simulation.WordOutput

/-!
# A library recursive program for bounded recognition and fallback

The program computes the bounded native recognizer's candidate, then decodes
the standard word encoding into reversed symbol codes. Its evaluation theorem
specifies the returned values, rather than only the domain of evaluation. This
is the program to be run between the native random-input and output routines.
-/

namespace ComplexityOfGenerators

open Simulation Turing ToPartrec Encodable

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Primcodable α] (M : Machine α Bool Unit) (fallback : List α)

private theorem exists_clockedCandidateCode : ∃ code : Code, ∀ clock candidate : ℕ,
    code.eval [clock, candidate] = Part.some [encode (clockedCandidate M fallback clock candidate)] := by
  have computation : Primrec₂ (fun clock candidate : ℕ =>
      encode (clockedCandidate M fallback clock candidate)) :=
    (Primrec.encode.comp (primrec_clockedCandidate M fallback)).to₂
  obtain ⟨code, correct⟩ := Code.exists_code
    (Nat.Partrec'.part_iff₂.mpr computation.to_comp.partrec.to₂)
  refine ⟨code, fun clock candidate => ?_⟩
  exact correct (⟨[clock, candidate], rfl⟩ : List.Vector ℕ 2)

noncomputable def clockedCandidateCode : Code := (exists_clockedCandidateCode M fallback).choose

theorem clockedCandidateCode_eval (clock candidate : ℕ) :
    (clockedCandidateCode M fallback).eval [clock, candidate] =
      Part.some [encode (clockedCandidate M fallback clock candidate)] :=
  (exists_clockedCandidateCode M fallback).choose_spec clock candidate

/-- This concrete library program returns the symbol codes in the order needed
by the subsequent native stack-scanning output routine. -/
noncomputable def clockedWordCode : Code :=
  .comp wordDecodeCode (clockedCandidateCode M fallback)

theorem clockedWordCode_eval (clock candidate : ℕ) :
    (clockedWordCode M fallback).eval [clock, candidate] =
      Part.some ((clockedCandidate M fallback clock candidate).reverse.map encode) := by
  change ((clockedCandidateCode M fallback).eval [clock, candidate]).bind
    (fun input => wordDecodeCode.eval input) = _
  rw [clockedCandidateCode_eval, Part.bind_some, wordDecodeCode_word]

/-- In particular, every sampled pair gives a terminating computation. -/
theorem clockedWordCode_total (clock candidate : ℕ) :
    ((clockedWordCode M fallback).eval [clock, candidate]).Dom := by
  rw [clockedWordCode_eval]
  trivial

theorem clockedWordCode_sound {L : Language α} (fallbackMember : fallback ∈ L)
    (recognizes : ∀ word, M.Accepts (decisionData word) [] ↔ word ∈ L)
    (clock candidate : ℕ) :
    ∃ word ∈ L, (clockedWordCode M fallback).eval [clock, candidate] =
      Part.some (word.reverse.map encode) :=
  ⟨clockedCandidate M fallback clock candidate,
    clockedCandidate_sound M fallback fallbackMember recognizes clock candidate,
    clockedWordCode_eval M fallback clock candidate⟩

theorem clockedWordCode_complete (word : List α)
    (accepted : M.Accepts (decisionData word) []) :
    ∃ clock, (clockedWordCode M fallback).eval [clock, encode word] =
      Part.some (word.reverse.map encode) := by
  obtain ⟨output, clock, run⟩ := accepted
  have test : acceptingResult M (finiteRun M (decisionData word) [] clock) = true :=
    (acceptingResult_correct M _).mpr
      ⟨output, (finiteRun_accepts_iff M (decisionData word) [] clock output).mpr run⟩
  refine ⟨clock, ?_⟩
  rw [clockedWordCode_eval]
  simp [clockedCandidate, test]

end ComplexityOfGenerators
