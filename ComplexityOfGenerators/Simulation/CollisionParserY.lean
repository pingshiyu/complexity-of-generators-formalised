import ComplexityOfGenerators.Simulation.CollisionParserFinish

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

def CollisionYResult (word x y rest : BitString) (t : ℕ) : Prop :=
  match readCollisionBits rest with
  | none => (collisionBank M).Executes word (collisionYConfiguration M x y) t false
  | some tail =>
      if x.length = (y ++ tail).length ∧ x ≠ y ++ tail then
        (collisionBank M).Steps word (collisionYConfiguration M x y) t
          (collisionParsedConfiguration M word x (y ++ tail))
      else (collisionBank M).Executes word (collisionYConfiguration M x y) t false

theorem collision_parse_y (word x y rest : BitString) (bound : y.length ≤ x.length)
    (encoding : word = collisionBits x ++ true :: false :: (collisionBits y ++ rest)) :
    ∃ t, t ≤ 4 * rest.length + 3 * x.length + 4 ∧ CollisionYResult M word x y rest t := by
  induction rest using (measure List.length).wf.induction generalizing word y with
  | h rest ih =>
    cases rest with
    | nil =>
        have enc : word = collisionBits x ++ true :: false :: collisionBits y := by simpa using encoding
        by_cases valid : x.length = y.length ∧ x ≠ y
        · refine ⟨2 * y.length + (x.length - 1) + 4, by simp only [List.length_nil]; omega, ?_⟩
          simpa [CollisionYResult, readCollisionBits, valid] using collisionY_finish M word x y enc valid.1 valid.2
        · refine ⟨0, by omega, ?_⟩
          have read : word[2 * x.length + 2 + 2 * y.length]? = none := by
            apply List.getElem?_eq_none
            simp [enc]; omega
          have rejected : (collisionBank M).Executes word (collisionYConfiguration M x y) 0 false := by
            apply TapeBank.Executes.reject
            by_cases equal : y.length = x.length
            · have same : x = y := by tauto
              subst y
              simp [TapeBank.instruction, collisionBank, collisionYConfiguration, collisionSelect,
                collisionTransition, collisionLoadedTapes, read]
            · have inside : y.length < x.length := by omega
              simp [TapeBank.instruction, collisionBank, collisionYConfiguration, collisionSelect,
                collisionTransition, collisionLoadedTapes, read, List.getElem?_eq_getElem inside]
          simpa [CollisionYResult, readCollisionBits, valid] using rejected
    | cons a tail =>
      cases a with
      | true =>
          refine ⟨0, by omega, ?_⟩
          apply TapeBank.Executes.reject
          have read : word[2 * x.length + 2 + 2 * y.length]? = some true := by
            have enc : word = (collisionBits x ++ [true, false] ++ collisionBits y) ++ true :: tail := by
              simpa [List.append_assoc] using encoding
            have len : (collisionBits x ++ [true, false] ++ collisionBits y).length =
                2 * x.length + 2 + 2 * y.length := by simp; omega
            rw [enc, ← len, List.getElem?_append_right (Nat.le_refl _)]
            simp
          simp [TapeBank.instruction, collisionBank, collisionYConfiguration, collisionSelect, collisionTransition, read]
      | false =>
        cases tail with
        | nil =>
            have first := collisionY_read_header M word x y [] encoding
            refine ⟨1, by simp, ?_⟩
            apply first.executes (collisionBank M) (t := 0)
            apply TapeBank.Executes.reject
            have read : word[2 * x.length + 2 + 2 * y.length + 1]? = none := by
              apply List.getElem?_eq_none
              simp [encoding]; omega
            simp [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition, read]
        | cons b rest =>
          by_cases inside : y.length < x.length
          · have current : x[y.length]? = some x[y.length] := List.getElem?_eq_getElem inside
            have first := collisionY_load_bit M word x y rest x[y.length] b encoding current
            have enc : word = collisionBits x ++ true :: false :: (collisionBits (y ++ [b]) ++ rest) := by
              simpa [List.append_assoc] using encoding
            obtain ⟨t, cost, result⟩ := ih rest (by change rest.length < (false :: b :: rest).length; simp)
              word (y ++ [b]) (by simp; omega) enc
            refine ⟨3 + t, by simp only [List.length_cons] at *; omega, ?_⟩
            cases read : readCollisionBits rest with
            | none =>
                have rejected : (collisionBank M).Executes word (collisionYConfiguration M x (y ++ [b])) t false := by
                  simpa [CollisionYResult, read] using result
                simpa [CollisionYResult, readCollisionBits, read] using first.executes (collisionBank M) rejected
            | some tail =>
                by_cases valid : x.length = (y ++ b :: tail).length ∧ x ≠ y ++ b :: tail
                · have path : (collisionBank M).Steps word (collisionYConfiguration M x (y ++ [b])) t
                      (collisionParsedConfiguration M word x (y ++ b :: tail)) := by
                    simpa [CollisionYResult, read, List.append_assoc, valid] using result
                  simpa [CollisionYResult, readCollisionBits, read, valid] using first.trans (collisionBank M) path
                · simp only [List.length_append, List.length_cons] at valid
                  have rejected : (collisionBank M).Executes word (collisionYConfiguration M x (y ++ [b])) t false := by
                    simpa [CollisionYResult, read, List.append_assoc, valid] using result
                  simpa [CollisionYResult, readCollisionBits, read, valid] using first.executes (collisionBank M) rejected
          · have equal : y.length = x.length := by omega
            have first := collisionY_read_header M word x y (b :: rest) encoding
            have rejected : (collisionBank M).Executes word
                {collisionYConfiguration M x y with
                  state := .yBit (decide (x.take y.length ≠ y))
                  inputHead := 2 * x.length + 2 + 2 * y.length + 1} 0 false := by
              apply TapeBank.Executes.reject
              simp only [TapeBank.instruction, collisionBank, collisionSelect, collisionTransition]
              simp [collisionYConfiguration, collisionLoadedTapes, equal]
            refine ⟨1, by simp, ?_⟩
            have run := first.executes (collisionBank M) rejected
            cases read : readCollisionBits rest with
            | none => simpa [CollisionYResult, readCollisionBits, read] using run
            | some tail =>
                have invalid : ¬ x.length = (y ++ b :: tail).length := by simp; omega
                simp only [List.length_append, List.length_cons] at invalid
                simpa [CollisionYResult, readCollisionBits, read, invalid] using run

end
end ComplexityOfGenerators.Simulation
