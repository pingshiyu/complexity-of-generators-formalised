import ComplexityOfGenerators.Simulation.RandomTranscript
import ComplexityOfGenerators.Simulation.CertificateVerifier

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I O : Type} [Fintype O] (M : Machine I Bool O)

/-- Exact agreement with deterministic replay. Exhaustion of the random
transcript becomes the verifier's explicit rejection. -/
theorem randomTranscript_replay_from (input : List I) (n : ℕ) (log : BitString)
    (c : Configuration M) (lead : BitString)
    (inputBound : c.inputHead ≤ input.length) (indexBound : c.indexHead ≤ n) (head : c.workHead ∈ c.visited) :
    ∃ result,
      (randomTranscript M).runFrom (transcriptSourceData input n) (lead ++ log)
        (randomTranscriptConfiguration M c lead.length) (2 * log.length) = .halted result ∧
      (transcriptReplay M).runFrom (transcriptData input n (lead ++ log)) []
        (transcriptConfiguration M c lead.length) log.length = .halted (certificateOutcome result) := by
  induction log generalizing c lead with
  | nil =>
      cases action : M.transition c.state input[c.inputHead]? none
          (if c.indexHead < n then some () else none) (c.work c.workHead) with
      | accept =>
          exact ⟨.accepted c.output, by simp [Machine.runFrom, Machine.observe, randomTranscript,
            randomTranscriptConfiguration, transcriptSourceData, randomTranscriptInstruction, action],
            by simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action, certificateOutcome]⟩
      | reject =>
          exact ⟨.rejected, by simp [Machine.runFrom, Machine.observe, randomTranscript,
            randomTranscriptConfiguration, transcriptSourceData, randomTranscriptInstruction, action],
            by simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action, certificateOutcome]⟩
      | step state write work ordinary auxiliary index emit =>
          exact ⟨.exhausted, by simp [Machine.runFrom, Machine.observe, randomTranscript,
            randomTranscriptConfiguration, transcriptSourceData, randomTranscriptInstruction, action],
            by simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action, certificateOutcome]⟩
      | readRandom no yes =>
          exact ⟨.exhausted, by simp [Machine.runFrom, Machine.observe, randomTranscript,
            randomTranscriptConfiguration, transcriptSourceData, randomTranscriptInstruction, action],
            by simp [Machine.runFrom, Machine.observe, transcriptReplay, transcriptConfiguration,
              transcriptData, transcriptInstruction, action, certificateOutcome]⟩
  | cons bit tail ih =>
      have lookup : (lead ++ bit :: tail)[lead.length]? = some bit := by
        rw [List.getElem?_append_right le_rfl]
        simp
      cases action : M.transition c.state input[c.inputHead]? none
          (if c.indexHead < n then some () else none) (c.work c.workHead) with
      | accept =>
          refine ⟨.accepted c.output, ?_, ?_⟩
          · apply Machine.runFrom_halted
            simp [Machine.observe, randomTranscript, randomTranscriptConfiguration, transcriptSourceData,
              randomTranscriptInstruction, action]
          · apply Machine.runFrom_halted
            simp [Machine.observe, transcriptReplay, transcriptConfiguration, transcriptData,
              transcriptInstruction, action, certificateOutcome]
      | reject =>
          refine ⟨.rejected, ?_, ?_⟩
          · apply Machine.runFrom_halted
            simp [Machine.observe, randomTranscript, randomTranscriptConfiguration, transcriptSourceData,
              randomTranscriptInstruction, action]
          · apply Machine.runFrom_halted
            simp [Machine.observe, transcriptReplay, transcriptConfiguration, transcriptData,
              transcriptInstruction, action, certificateOutcome]
      | step state write work ordinary auxiliary index emit =>
          obtain ⟨result, random, replay⟩ := ih
            (M.stepConfiguration (transcriptSourceData input n) c state write work ordinary auxiliary index emit)
            (lead ++ [bit]) (ordinary.onInput_le _ _ inputBound) (index.onInput_le _ _ indexBound)
            (Finset.mem_insert_self _ _)
          have steps := randomTranscript_step M input n (lead ++ bit :: tail) c lead.length bit
            state write work ordinary auxiliary index emit action lookup
          have one := transcriptReplay_step M input n lead bit tail [] c
            state write work ordinary auxiliary index emit action
          refine ⟨result, ?_, ?_⟩
          · rw [List.length_cons, show 2 * (tail.length + 1) = 2 + 2 * tail.length by omega,
              (randomTranscript M).runFrom_add _ _ _ _ 2 steps]
            simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] using random
          · rw [List.length_cons, (transcriptReplay M).runFrom_shift _ _ _ _ one.1 one.2]
            simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] using replay
      | readRandom no yes =>
          obtain ⟨result, random, replay⟩ := ih {c with state := if bit then yes else no, randomHead := 0}
            (lead ++ [bit]) inputBound indexBound head
          have steps := randomTranscript_random M input n (lead ++ bit :: tail) c lead.length bit no yes
            inputBound indexBound head action lookup
          have one := transcriptReplay_random M input n lead bit tail [] c no yes inputBound indexBound head action
          refine ⟨result, ?_, ?_⟩
          · rw [List.length_cons, show 2 * (tail.length + 1) = 2 + 2 * tail.length by omega,
              (randomTranscript M).runFrom_add _ _ _ _ 2 steps]
            simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] using random
          · rw [List.length_cons, (transcriptReplay M).runFrom_shift _ _ _ _ one.1 one.2]
            simpa only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] using replay

theorem randomTranscript_boot (input : List I) (n : ℕ) (padding : Bool) (log : BitString) :
    (randomTranscript M).observe (transcriptSourceData input n) (padding :: log)
        (randomTranscript M).initialConfiguration = .running (randomTranscript M).initialConfiguration ∧
      (randomTranscript M).next (transcriptSourceData input n) (padding :: log)
        (randomTranscript M).initialConfiguration =
        .running (randomTranscriptConfiguration M M.initialConfiguration 1) := by
  simp [Machine.observe, Machine.next, randomTranscript, Machine.initialConfiguration, randomTranscriptConfiguration]

/-- The adapter halts on every finite transcript in at most twice its length
plus one, and agrees with replay on every accepted output. -/
theorem randomTranscript_replay (input : List I) (n : ℕ) (certificate : BitString) :
    ∃ result,
      (randomTranscript M).run (transcriptSourceData input n) certificate (2 * certificate.length + 1) = .halted result ∧
      (transcriptReplay M).run (transcriptData input n certificate) [] certificate.length =
        .halted (certificateOutcome result) := by
  cases certificate with
  | nil =>
      refine ⟨.exhausted, ?_, ?_⟩
      · simp [Machine.run, Machine.observe, randomTranscript, Machine.initialConfiguration]
      · exact transcriptReplay_empty_certificate M input n []
  | cons padding log =>
      obtain ⟨result, random, replay⟩ := randomTranscript_replay_from M input n log M.initialConfiguration [padding]
        (Nat.zero_le _) (Nat.zero_le _) (Finset.mem_singleton_self _)
      obtain ⟨live, next⟩ := randomTranscript_boot M input n padding log
      have execution : (randomTranscript M).run (transcriptSourceData input n) (padding :: log)
          (2 * log.length + 1) = .halted result := by
        rw [← Machine.runFrom_initial, (randomTranscript M).runFrom_shift _ _ _ _ live next]
        exact random
      refine ⟨result, ?_, ?_⟩
      · have later := (randomTranscript M).run_halted_add _ _ _ _ execution 2
        simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 1 2] using later
      · obtain ⟨live, next⟩ := transcriptReplay_boot M input n padding log []
        rw [List.length_cons, ← Machine.runFrom_initial,
          (transcriptReplay M).runFrom_shift _ _ _ _ live next]
        exact replay

end
end ComplexityOfGenerators.Simulation
