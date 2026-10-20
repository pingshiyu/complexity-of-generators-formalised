import ComplexityOfGenerators.Proofs.ExactRecursiveAlgorithm
import ComplexityOfGenerators.Proofs.ExactRecursiveLabels

/-! The checked walk for any complete finite label enumeration. This allows
the native word counter to reuse the existing inverse-trial and path proofs. -/

namespace ComplexityOfGenerators

structure LabelEnumeration {α : Type} {L : Language α} (R : SelfReduction L) where
  words : ℕ → List (Word α)
  bound : PolynomialBound
  length_le : ∀ n, (words n).length ≤ bound n
  covers : ∀ {n : ℕ} {x y w : Word α}, x ∈ R.inverseFibre n y w → w ∈ words n

namespace LabelEnumeration

noncomputable def shortlex {α : Type} [Fintype α] {L : Language α} (R : SelfReduction L)
    (alphabet : List α) (card : alphabet.length = Fintype.card α)
    (first : α) (least : Simulation.CyclicGenerator.firstLetter = some first) : LabelEnumeration R where
  words n := Simulation.WordStack.Shortlex.labels first (R.labelCountBound alphabet n)
  bound := R.labelCountBound alphabet
  length_le n := by simp
  covers := R.inverse_label_in_shortlex alphabet card first least

end LabelEnumeration

namespace ExactRecursiveGenerators

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : ExactRecursiveGenerators R)

def tableEntries (E : LabelEnumeration R) (n : ℕ) (y : Word α) : List (BitString → Option (Word α)) :=
  (E.words n).map (G.positiveTrial n y)

def tableSeed (E : LabelEnumeration R) (n : ℕ) : ℕ :=
  (E.words n).length * (G.inverseSeed n + 1)

def tableSearch (E : LabelEnumeration R) (n : ℕ) (y : Word α) (bits : BitString) : Option (Word α) :=
  BoundedTrialChoice.run (G.inverseSeed n) (G.tableEntries E n y) bits

theorem table_seed_eq (E : LabelEnumeration R) (n : ℕ) (y : Word α) :
    G.tableSeed E n = BoundedTrialChoice.seedLength (G.inverseSeed n)
      (G.tableEntries E n y) := by
  simp [tableSeed, BoundedTrialChoice.seedLength, tableEntries]

theorem tableSearch_sound {E : LabelEnumeration R} {n : ℕ} {y x : Word α}
    (ancestor : y ∈ R.ancestors n) {bits : BitString}
    (length : bits.length = G.tableSeed E n)
    (output : G.tableSearch E n y bits = some x) : R.Up n y x := by
  obtain ⟨trial, member, seed, size, result⟩ := BoundedTrialChoice.sound
    (length.trans (G.table_seed_eq E n y)) output
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp member
  by_cases empty : w = []
  · simp [positiveTrial, empty] at result
  · exact ⟨w, empty, G.inverseTrial_sound ancestor.1 size (by simpa [positiveTrial, empty] using result)⟩

theorem tableSearch_complete (E : LabelEnumeration R) 
    {n : ℕ} {y x : Word α} (ancestor : y ∈ R.ancestors n) (step : R.Up n y x) :
    ∃ bits, bits.length = G.tableSeed E n ∧ G.tableSearch E n y bits = some x := by
  obtain ⟨w, nonempty, target⟩ := step
  obtain ⟨seed, size, result⟩ := G.inverseTrial_complete ancestor.1 target
  have member : G.positiveTrial n y w ∈ G.tableEntries E n y :=
    List.mem_map.mpr ⟨w, E.covers target, rfl⟩
  obtain ⟨bits, length, output⟩ := BoundedTrialChoice.complete member size
    (show G.positiveTrial n y w seed = some x by simpa [positiveTrial, nonempty] using result)
  exact ⟨bits, length.trans (G.table_seed_eq E n y).symm, output⟩

theorem tableSearch_total (E : LabelEnumeration R)
    {n : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n) (short : y.length < n)
    {bits : BitString} (length : bits.length = G.tableSeed E n) :
    ∃ x, G.tableSearch E n y bits = some x := by
  obtain ⟨w, nonempty, z, target⟩ := R.ancestor_progress ancestor short
  apply BoundedTrialChoice.total_of_entry
    (List.mem_map.mpr ⟨w, E.covers target, rfl⟩ : G.positiveTrial n y w ∈ G.tableEntries E n y)
    _ (length.trans (G.table_seed_eq E n y))
  intro seed size
  obtain ⟨x, output⟩ := (G.inverseTrial_success_iff ancestor.1 seed size).mpr ⟨z, target⟩
  exact ⟨x, by simpa [positiveTrial, nonempty] using output⟩

def tableWalkSeed (E : LabelEnumeration R) (n fuel : ℕ) : ℕ := fuel * (1 + G.tableSeed E n)

def tableWalk (E : LabelEnumeration R) (n : ℕ) : ℕ → Word α → BitString → Option (Word α)
  | 0, y, _ => if y.length = n then some y else none
  | fuel + 1, y, bits =>
    if y.length = n ∧ bits.head? = some true then some y
    else match G.tableSearch E n y ((bits.drop 1).take (G.tableSeed E n)) with
      | none => if y.length = n then some y else none
      | some z => tableWalk E n fuel z (bits.drop (1 + G.tableSeed E n))

theorem tableWalk_split_lengths (E : LabelEnumeration R) (n fuel : ℕ) {bits : BitString}
    (length : bits.length = G.tableWalkSeed E n (fuel + 1)) :
    ((bits.drop 1).take (G.tableSeed E n)).length = G.tableSeed E n ∧
      (bits.drop (1 + G.tableSeed E n)).length = G.tableWalkSeed E n fuel := by
  simp only [tableWalkSeed, Nat.add_mul] at length
  simp only [List.length_take, List.length_drop, tableWalkSeed]
  constructor <;> omega

theorem tableWalk_sound {E : LabelEnumeration R} {n fuel : ℕ} {y x : Word α}
    (ancestor : y ∈ R.ancestors n) {bits : BitString}
    (length : bits.length = G.tableWalkSeed E n fuel)
    (output : G.tableWalk E n fuel y bits = some x) : x ∈ R.walkOutputs n fuel y := by
  induction fuel generalizing y bits with
  | zero =>
    by_cases equal : y.length = n
    · exact ⟨(Option.some.inj (by simpa only [tableWalk, ite_eq_left equal] using output)).symm, equal⟩
    · simp [tableWalk, equal] at output
  | succ fuel ih =>
    obtain ⟨searchLength, restLength⟩ := G.tableWalk_split_lengths E n fuel length
    simp only [tableWalk] at output
    by_cases stop : y.length = n ∧ bits.head? = some true
    · rw [ite_eq_left stop] at output
      exact Or.inl ⟨(Option.some.inj output).symm, stop.1⟩
    · rw [ite_eq_right stop] at output
      cases search : G.tableSearch E n y ((bits.drop 1).take (G.tableSeed E n)) with
      | none =>
        simp only [search] at output
        by_cases equal : y.length = n
        · rw [ite_eq_left equal] at output
          exact Or.inl ⟨(Option.some.inj output).symm, equal⟩
        · simp [equal] at output
      | some z =>
        simp only [search] at output
        have step := G.tableSearch_sound ancestor searchLength search
        exact Or.inr ⟨z, step, ih (R.up_iff.mp step).1 restLength output⟩

theorem tableWalk_block (E : LabelEnumeration R) (n fuel : ℕ) (y : Word α)
    (bit : Bool) (searchBits rest : BitString) (length : searchBits.length = G.tableSeed E n) :
    G.tableWalk E n (fuel + 1) y (bit :: (searchBits ++ rest)) =
      if y.length = n ∧ bit = true then some y
      else match G.tableSearch E n y searchBits with
        | none => if y.length = n then some y else none
        | some z => G.tableWalk E n fuel z rest := by
  simp [tableWalk, ← length, List.drop_append, Nat.add_comm]

theorem tableWalk_complete (E : LabelEnumeration R) 
    {n fuel : ℕ} {y x : Word α} (ancestor : y ∈ R.ancestors n)
    (target : x ∈ R.walkOutputs n fuel y) :
    ∃ bits, bits.length = G.tableWalkSeed E n fuel ∧ G.tableWalk E n fuel y bits = some x := by
  induction fuel generalizing y with
  | zero =>
    obtain ⟨rfl, equal⟩ := target
    exact ⟨[], by simp [tableWalkSeed], by simp [tableWalk, equal]⟩
  | succ fuel ih =>
    rcases target with ⟨rfl, equal⟩ | ⟨z, step, target⟩
    · refine ⟨true :: List.replicate (G.tableWalkSeed E n (fuel + 1) - 1) false, ?_, ?_⟩
      · simp only [List.length_cons, List.length_replicate]
        have : 0 < G.tableWalkSeed E n (fuel + 1) := by unfold tableWalkSeed; positivity
        omega
      · simp [tableWalk, equal]
    · obtain ⟨searchBits, searchLength, search⟩ := G.tableSearch_complete E ancestor step
      obtain ⟨rest, restLength, output⟩ := ih (R.up_iff.mp step).1 target
      refine ⟨false :: (searchBits ++ rest), ?_, ?_⟩
      · simp only [List.length_cons, List.length_append, searchLength, restLength, tableWalkSeed]
        ring
      · rw [G.tableWalk_block E n fuel y false searchBits rest searchLength]
        simpa [search] using output

/-- No full seed fails when the starting ancestor has enough remaining rank.
In particular, declining the stop coin cannot get stuck at a short word. -/
theorem tableWalk_total (E : LabelEnumeration R) 
    {n fuel : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n)
    (enough : R.rankBound n ≤ R.rank y + fuel) {bits : BitString}
    (length : bits.length = G.tableWalkSeed E n fuel) :
    ∃ x, G.tableWalk E n fuel y bits = some x := by
  induction fuel generalizing y bits with
  | zero =>
    obtain ⟨x, equal, size⟩ := R.walk_nonempty ancestor enough
    subst x
    exact ⟨y, by simp [tableWalk, size]⟩
  | succ fuel ih =>
    obtain ⟨searchLength, restLength⟩ := G.tableWalk_split_lengths E n fuel length
    simp only [tableWalk]
    by_cases stop : y.length = n ∧ bits.head? = some true
    · rw [ite_eq_left stop]
      exact ⟨y, rfl⟩
    · rw [ite_eq_right stop]
      cases search : G.tableSearch E n y ((bits.drop 1).take (G.tableSeed E n)) with
      | none =>
        have equal : y.length = n := by
          by_contra different
          obtain ⟨z, success⟩ := G.tableSearch_total E ancestor
            (by have := R.ancestor_length_le ancestor; omega) searchLength
          rw [search] at success
          contradiction
        exact ⟨y, by simp [equal]⟩
      | some z =>
        have step := G.tableSearch_sound ancestor searchLength search
        have increase := R.step_rank_lt (R.up_iff.mp step).2
        exact ih (R.up_iff.mp step).1 (by omega) restLength

theorem tableWalk_append (E : LabelEnumeration R) (n fuel : ℕ) (y : Word α)
    {bits : BitString} (length : bits.length = G.tableWalkSeed E n fuel) (extra : BitString) :
    G.tableWalk E n fuel y (bits ++ extra) = G.tableWalk E n fuel y bits := by
  induction fuel generalizing y bits with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨searchLength, restLength⟩ := G.tableWalk_split_lengths E n fuel length
    have enough : 1 + G.tableSeed E n ≤ bits.length := by
      simp only [tableWalkSeed, Nat.add_mul] at length
      omega
    have first : (bits ++ extra).head? = bits.head? := by
      cases bits with
      | nil => simp only [List.length_nil] at enough; omega
      | cons bit tail => rfl
    have search : ((bits ++ extra).drop 1).take (G.tableSeed E n) =
        (bits.drop 1).take (G.tableSeed E n) := by
      rw [List.drop_append_of_le_length (by omega : 1 ≤ bits.length)]
      exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)
    have rest : (bits ++ extra).drop (1 + G.tableSeed E n) =
        bits.drop (1 + G.tableSeed E n) ++ extra := List.drop_append_of_le_length enough
    rw [tableWalk, tableWalk, first, search, rest]
    by_cases stop : y.length = n ∧ bits.head? = some true
    · rw [ite_eq_left stop, ite_eq_left stop]
    · rw [ite_eq_right stop, ite_eq_right stop]
      cases G.tableSearch E n y ((bits.drop 1).take (G.tableSeed E n)) with
      | none => rfl
      | some z => exact ih z restLength



end ExactRecursiveGenerators
end ComplexityOfGenerators
