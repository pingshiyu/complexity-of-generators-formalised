import ComplexityOfGenerators.Simulation.CollisionParserSeparator

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

def CollisionXResult (word x rest : BitString) (t : ℕ) : Prop :=
  match splitCollisionInput rest with
  | none => (collisionBank M).Executes word (collisionXConfiguration M x) t false
  | some (tail, _) =>
      if x ++ tail = [] then (collisionBank M).Executes word (collisionXConfiguration M x) t false
      else (collisionBank M).Steps word (collisionXConfiguration M x) t
        (collisionYConfiguration M (x ++ tail) [])

/-- The first parser loop either rejects malformed input, or loads a positive
first preimage and enters the second loop. Its bound includes rewinding. -/
theorem collision_parse_x (word x rest : BitString)
    (encoding : word = collisionBits x ++ rest) :
    ∃ t, t ≤ 4 * rest.length + x.length + 3 ∧ CollisionXResult M word x rest t := by
  induction rest using (measure List.length).wf.induction generalizing x word with
  | h rest ih =>
    cases rest with
    | nil =>
        refine ⟨0, by omega, ?_⟩
        apply TapeBank.Executes.reject
        have read : word[2 * x.length]? = none := by
          rw [encoding, ← collisionBits_length x]
          simp
        simp [TapeBank.instruction, collisionBank, collisionXConfiguration,
          collisionSelect, collisionTransition, read]
    | cons a tail =>
      cases tail with
      | nil =>
        cases a with
        | false =>
            have first := collisionX_read_header M word x [] encoding
            refine ⟨1, by simp, ?_⟩
            apply first.executes (collisionBank M) (t := 0)
            apply TapeBank.Executes.reject
            have read : word[2 * x.length + 1]? = none := by
              rw [encoding, ← collisionBits_length x]
              simp
            simp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition, read]
        | true =>
            have first := collisionX_read_separator M word x [] encoding
            refine ⟨1, by simp, ?_⟩
            apply first.executes (collisionBank M) (t := 0)
            apply TapeBank.Executes.reject
            have read : word[2 * x.length + 1]? = none := by
              rw [encoding, ← collisionBits_length x]
              simp
            simp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition, read]
      | cons b rest =>
        cases a with
        | false =>
            obtain ⟨s, cost, step⟩ := collisionX_load_bit M word x b rest encoding
            have encoding' : word = collisionBits (x ++ [b]) ++ rest := by simpa [List.append_assoc] using encoding
            obtain ⟨t, cost', result⟩ := ih rest (by change rest.length < (false :: b :: rest).length; simp) word (x ++ [b]) encoding'
            refine ⟨s + t, by simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil] at *; omega, ?_⟩
            cases read : splitCollisionInput rest with
            | none =>
                have rejected : (collisionBank M).Executes word (collisionXConfiguration M (x ++ [b])) t false := by
                  simpa [CollisionXResult, read] using result
                simpa [CollisionXResult, splitCollisionInput, read] using step.executes (collisionBank M) rejected
            | some pair =>
                obtain ⟨tail, remaining⟩ := pair
                have path : (collisionBank M).Steps word (collisionXConfiguration M (x ++ [b])) t
                    (collisionYConfiguration M (x ++ b :: tail) []) := by
                  simpa [CollisionXResult, read, List.append_assoc] using result
                simpa [CollisionXResult, splitCollisionInput, read] using step.trans (collisionBank M) path
        | true =>
          cases b with
          | false =>
              by_cases positive : x = []
              · subst x
                have first := collisionX_read_separator M word [] (false :: rest) encoding
                refine ⟨1, by simp, ?_⟩
                apply first.executes (collisionBank M) (t := 0)
                apply TapeBank.Executes.reject
                simp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition]
              · refine ⟨x.length + 3, by simp, ?_⟩
                simpa [CollisionXResult, splitCollisionInput, positive] using
                  collisionX_separator M word x rest positive encoding
          | true =>
              have first := collisionX_read_separator M word x (true :: rest) encoding
              refine ⟨1, by simp, ?_⟩
              apply first.executes (collisionBank M) (t := 0)
              apply TapeBank.Executes.reject
              have read : word[2 * x.length + 1]? = some true := by
                rw [encoding, ← collisionBits_length x]
                simp
              simp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition, read]

end
end ComplexityOfGenerators.Simulation
