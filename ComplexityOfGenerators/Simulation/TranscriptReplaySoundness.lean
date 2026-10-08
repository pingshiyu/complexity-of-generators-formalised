import ComplexityOfGenerators.Simulation.TranscriptReplayCorrectness

/-! Acceptance by the native replay machine implies a genuine source
transcript, even for malformed or overlong certificates. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I O : Type} (M : Machine I Bool O)

theorem transcriptReplay_to_trace (input : List I) (n : ℕ) (log : BitString) (out : List O)
    (c : Configuration M) (lead bits : BitString)
    (inputBound : c.inputHead ≤ input.length) (indexBound : c.indexHead ≤ n)
    (head : c.workHead ∈ c.visited)
    (accepted : (transcriptReplay M).runFrom (transcriptData input n (lead ++ log)) bits
      (transcriptConfiguration M c lead.length) log.length = .halted (.accepted out)) :
    M.AcceptingTranscript (transcriptSourceData input n) c log out := by
  induction log generalizing c lead with
  | nil =>
      cases action : M.transition c.state input[c.inputHead]? none
          (if c.indexHead < n then some true else none) (c.work c.workHead) with
      | accept =>
          have same : c.output = out := by
            simpa [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action] using accepted
          rw [← same]
          exact .accept c [] (by simpa [transcriptSourceData] using action)
      | reject =>
          simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
            transcriptData, transcriptInstruction, action] at accepted
      | readRandom no yes =>
          simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
            transcriptData, transcriptInstruction, action] at accepted
      | step state write work ordinary auxiliary index emit =>
          simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
            transcriptData, transcriptInstruction, action] at accepted
  | cons bit tail ih =>
      cases action : M.transition c.state input[c.inputHead]? none
          (if c.indexHead < n then some true else none) (c.work c.workHead) with
      | accept =>
          have terminal : (transcriptReplay M).observe (transcriptData input n (lead ++ bit :: tail)) bits
              (transcriptConfiguration M c lead.length) = .halted (.accepted c.output) := by
            simp [Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action]
          have same := (transcriptReplay M).runFrom_halted _ bits _ _ terminal (bit :: tail).length
          rw [accepted] at same
          have outputEq := Outcome.accepted.inj (RunState.halted.inj same)
          rw [outputEq]
          exact .accept c (bit :: tail) (by simpa [transcriptSourceData] using action)
      | reject =>
          have terminal : (transcriptReplay M).observe (transcriptData input n (lead ++ bit :: tail)) bits
              (transcriptConfiguration M c lead.length) = .halted .rejected := by
            simp [Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action]
          have same := (transcriptReplay M).runFrom_halted _ bits _ _ terminal (bit :: tail).length
          rw [accepted] at same
          cases same
      | step state write work ordinary auxiliary index emit =>
          obtain ⟨live, next⟩ := transcriptReplay_step M input n lead bit tail bits c
            state write work ordinary auxiliary index emit action
          simp only [List.length_cons] at accepted
          rw [(transcriptReplay M).runFrom_shift _ bits _ _ live next tail.length] at accepted
          have continuation := ih
            (M.stepConfiguration (transcriptSourceData input n) c state write work ordinary auxiliary index emit)
            (lead ++ [bit]) (ordinary.onInput_le _ _ inputBound) (index.onInput_le _ _ indexBound)
            (Finset.mem_insert_self _ _)
            (by simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
                using accepted)
          exact .step c bit tail out state write work ordinary auxiliary index emit
            (by simpa [transcriptSourceData] using action) continuation
      | readRandom no yes =>
          obtain ⟨live, next⟩ := transcriptReplay_random M input n lead bit tail bits c
            no yes inputBound indexBound head action
          simp only [List.length_cons] at accepted
          rw [(transcriptReplay M).runFrom_shift _ bits _ _ live next tail.length] at accepted
          have continuation := ih {c with state := if bit then yes else no, randomHead := 0}
            (lead ++ [bit]) inputBound indexBound head
            (by simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
                using accepted)
          exact .random c bit tail out no yes (by simpa [transcriptSourceData] using action) continuation

theorem transcriptReplay_run_iff_trace (input : List I) (n : ℕ) (padding : Bool)
    (log : BitString) (out : List O) (bits : BitString) :
    (transcriptReplay M).run (transcriptData input n (padding :: log)) bits (log.length + 1) =
        .halted (.accepted out) ↔
      M.AcceptingTranscript (transcriptSourceData input n) M.initialConfiguration log out := by
  constructor
  · intro accepted
    obtain ⟨live, next⟩ := transcriptReplay_boot M input n padding log bits
    rw [← Machine.runFrom_initial, (transcriptReplay M).runFrom_shift _ bits _ _ live next log.length] at accepted
    exact transcriptReplay_to_trace M input n log out M.initialConfiguration [padding] bits
      (by simp [Machine.initialConfiguration]) (by simp [Machine.initialConfiguration])
      (by simp [Machine.initialConfiguration]) accepted
  · intro trace
    exact transcriptReplay_accepts_trace M input n log out trace padding bits

theorem transcriptReplay_sound (input : List I) (n : ℕ) (certificate bits : BitString) (out : List O)
    (accepted : (transcriptReplay M).run (transcriptData input n certificate) bits certificate.length =
      .halted (.accepted out)) :
    ∃ sourceBits, M.Produces (transcriptSourceData input n) sourceBits out := by
  cases certificate with
  | nil =>
      have rejected := transcriptReplay_empty_certificate M input n bits
      change (transcriptReplay M).run {input := input, index := n} bits 0 = .halted (.accepted out) at accepted
      rw [rejected] at accepted
      cases accepted
  | cons padding log =>
      exact ((transcriptReplay_run_iff_trace M input n padding log out bits).mp accepted).produces M

end
end ComplexityOfGenerators.Simulation
