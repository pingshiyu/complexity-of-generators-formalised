import ComplexityOfGenerators.Simulation.TranscriptReplaySteps

/-!
# Native replay of accepting source transcripts

The certificate begins with a padding bit, and the remaining bits correspond
to source instructions. Initialization and execution steps are charged.
These binary transcript lemmas support the retained certificate interface and
the current Proposition 6.1 via `Proofs.PaperCertificateEquivalence`.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I O : Type} (M : Machine I Bool O)

theorem transcriptReplay_of_trace (input : List I) (n : ℕ) (c : Configuration M)
    (log : BitString) (out : List O)
    (trace : M.AcceptingTranscript (transcriptSourceData input n) c log out)
    (lead bits : BitString) (inputBound : c.inputHead ≤ input.length) (indexBound : c.indexHead ≤ n)
    (head : c.workHead ∈ c.visited) :
    (transcriptReplay M).runFrom (transcriptData input n (lead ++ log)) bits
      (transcriptConfiguration M c lead.length) log.length = .halted (.accepted out) := by
  induction trace generalizing lead with
  | accept c suffix action =>
      apply Machine.runFrom_halted
      simp only [transcriptSourceData, List.getElem?_nil] at action
      simp [Machine.observe, transcriptReplay, transcriptConfiguration, transcriptData,
        transcriptInstruction, action]
  | step c bit tail out state write work ordinary auxiliary index emit action rest ih =>
      simp only [transcriptSourceData, List.getElem?_nil] at action
      obtain ⟨live, next⟩ := transcriptReplay_step M input n lead bit tail bits c
        state write work ordinary auxiliary index emit action
      have continuation := ih (lead ++ [bit])
        (ordinary.onInput_le _ _ inputBound) (index.onInput_le _ _ indexBound)
        (Finset.mem_insert_self _ _)
      simp only [List.length_cons]
      rw [(transcriptReplay M).runFrom_shift _ bits _ _ live next tail.length]
      simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
        using continuation
  | random c bit tail out no yes action rest ih =>
      simp only [transcriptSourceData, List.getElem?_nil] at action
      obtain ⟨live, next⟩ := transcriptReplay_random M input n lead bit tail bits c
        no yes inputBound indexBound head action
      have continuation := ih (lead ++ [bit]) inputBound indexBound head
      simp only [List.length_cons]
      rw [(transcriptReplay M).runFrom_shift _ bits _ _ live next tail.length]
      simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
        using continuation

theorem transcriptReplay_accepts_trace (input : List I) (n : ℕ) (log : BitString) (out : List O)
    (trace : M.AcceptingTranscript (transcriptSourceData input n) M.initialConfiguration log out)
    (padding : Bool) (bits : BitString) :
    (transcriptReplay M).run (transcriptData input n (padding :: log)) bits (log.length + 1) =
      .halted (.accepted out) := by
  obtain ⟨live, next⟩ := transcriptReplay_boot M input n padding log bits
  have continuation := transcriptReplay_of_trace M input n M.initialConfiguration log out trace [padding] bits
    (by simp [Machine.initialConfiguration]) (by simp [Machine.initialConfiguration])
    (by simp [Machine.initialConfiguration])
  rw [← Machine.runFrom_initial, (transcriptReplay M).runFrom_shift _ bits _ _ live next log.length]
  exact continuation

/-- An output accepted within `t` source steps has a positive binary
replay certificate of length at most `t+1`. The bound supports the current
Proposition 6.1 through `Proofs.PaperCertificateEquivalence`. -/
theorem transcriptReplay_complete (input : List I) (n : ℕ) (bits : BitString) (t : ℕ) (out : List O)
    (accepted : M.run (transcriptSourceData input n) bits t = .halted (.accepted out)) :
    ∃ certificate : BitString, certificate ≠ [] ∧ certificate.length ≤ t + 1 ∧
      (transcriptReplay M).run (transcriptData input n certificate) [] certificate.length =
        .halted (.accepted out) := by
  obtain ⟨log, length, trace⟩ := M.acceptingTranscript_of_runFrom (transcriptSourceData input n)
    bits M.initialConfiguration t out (by simpa only [Machine.runFrom_initial] using accepted)
  refine ⟨false :: log, by simp, by simp only [List.length_cons]; omega, ?_⟩
  exact transcriptReplay_accepts_trace M input n log out trace false []

end
end ComplexityOfGenerators.Simulation
