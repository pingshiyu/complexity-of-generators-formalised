import ComplexityOfGenerators.Proofs.ExactRecursiveTrials
import ComplexityOfGenerators.Proofs.BoundedTrialChoice

/-!
# The finite-seed algorithm for Proposition A.23.2

All inverse labels are tried on separate full seeds. Selection bits choose
among successful trials, with a successful fallback if all offers are declined.
The upward walk offers a stop at every length-`n` word, including intermediate
ones, and continues only along nonempty labels.
-/

namespace ComplexityOfGenerators.ExactRecursiveGenerators

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : ExactRecursiveGenerators R)

def positiveTrial (n : ℕ) (y w : Word α) (bits : BitString) : Option (Word α) :=
  if w = [] then none else G.inverseTrial n y w bits

def inverseEntries (alphabet : List α) (n : ℕ) (y : Word α) : List (BitString → Option (Word α)) :=
  (SelfReduction.wordsUpTo alphabet (R.labelWidth n)).map (G.positiveTrial n y)

def searchSeed (alphabet : List α) (n : ℕ) : ℕ :=
  (SelfReduction.wordsUpTo alphabet (R.labelWidth n)).length * (G.inverseSeed n + 1)

def inverseSearch (alphabet : List α) (n : ℕ) (y : Word α) (bits : BitString) : Option (Word α) :=
  BoundedTrialChoice.run (G.inverseSeed n) (G.inverseEntries alphabet n y) bits

theorem search_seed_eq (alphabet : List α) (n : ℕ) (y : Word α) :
    G.searchSeed alphabet n = BoundedTrialChoice.seedLength (G.inverseSeed n)
      (G.inverseEntries alphabet n y) := by
  simp [searchSeed, BoundedTrialChoice.seedLength, inverseEntries]

theorem inverseSearch_sound {alphabet : List α} {n : ℕ} {y x : Word α}
    (ancestor : y ∈ R.ancestors n) {bits : BitString}
    (length : bits.length = G.searchSeed alphabet n)
    (output : G.inverseSearch alphabet n y bits = some x) : R.Up n y x := by
  obtain ⟨trial, member, seed, size, result⟩ := BoundedTrialChoice.sound
    (length.trans (G.search_seed_eq alphabet n y)) output
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp member
  by_cases empty : w = []
  · simp [positiveTrial, empty] at result
  · exact ⟨w, empty, G.inverseTrial_sound ancestor.1 size (by simpa [positiveTrial, empty] using result)⟩

theorem inverseSearch_complete (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n : ℕ} {y x : Word α} (ancestor : y ∈ R.ancestors n) (step : R.Up n y x) :
    ∃ bits, bits.length = G.searchSeed alphabet n ∧ G.inverseSearch alphabet n y bits = some x := by
  obtain ⟨w, nonempty, target⟩ := step
  obtain ⟨seed, size, result⟩ := G.inverseTrial_complete ancestor.1 target
  have member : G.positiveTrial n y w ∈ G.inverseEntries alphabet n y :=
    List.mem_map.mpr ⟨w, R.inverse_label_mem alphabet complete target, rfl⟩
  obtain ⟨bits, length, output⟩ := BoundedTrialChoice.complete member size
    (show G.positiveTrial n y w seed = some x by simpa [positiveTrial, nonempty] using result)
  exact ⟨bits, length.trans (G.search_seed_eq alphabet n y).symm, output⟩

theorem inverseSearch_total (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n) (short : y.length < n)
    {bits : BitString} (length : bits.length = G.searchSeed alphabet n) :
    ∃ x, G.inverseSearch alphabet n y bits = some x := by
  obtain ⟨w, member, nonempty, succeeds⟩ := G.progress_full_trial alphabet complete ancestor short
  apply BoundedTrialChoice.total_of_entry
    (List.mem_map.mpr ⟨w, member, rfl⟩ : G.positiveTrial n y w ∈ G.inverseEntries alphabet n y)
    _ (length.trans (G.search_seed_eq alphabet n y))
  intro seed size
  obtain ⟨x, output, _⟩ := succeeds seed size
  exact ⟨x, by simpa [positiveTrial, nonempty] using output⟩

def walkSeed (alphabet : List α) (n fuel : ℕ) : ℕ := fuel * (1 + G.searchSeed alphabet n)

def walkTrial (alphabet : List α) (n : ℕ) : ℕ → Word α → BitString → Option (Word α)
  | 0, y, _ => if y.length = n then some y else none
  | fuel + 1, y, bits =>
    if y.length = n ∧ bits.head? = some true then some y
    else match G.inverseSearch alphabet n y ((bits.drop 1).take (G.searchSeed alphabet n)) with
      | none => if y.length = n then some y else none
      | some z => walkTrial alphabet n fuel z (bits.drop (1 + G.searchSeed alphabet n))

theorem walk_split_lengths (alphabet : List α) (n fuel : ℕ) {bits : BitString}
    (length : bits.length = G.walkSeed alphabet n (fuel + 1)) :
    ((bits.drop 1).take (G.searchSeed alphabet n)).length = G.searchSeed alphabet n ∧
      (bits.drop (1 + G.searchSeed alphabet n)).length = G.walkSeed alphabet n fuel := by
  simp only [walkSeed, Nat.add_mul] at length
  simp only [List.length_take, List.length_drop, walkSeed]
  constructor <;> omega

theorem walkTrial_sound {alphabet : List α} {n fuel : ℕ} {y x : Word α}
    (ancestor : y ∈ R.ancestors n) {bits : BitString}
    (length : bits.length = G.walkSeed alphabet n fuel)
    (output : G.walkTrial alphabet n fuel y bits = some x) : x ∈ R.walkOutputs n fuel y := by
  induction fuel generalizing y bits with
  | zero =>
    by_cases equal : y.length = n
    · exact ⟨(Option.some.inj (by simpa only [walkTrial, ite_eq_left equal] using output)).symm, equal⟩
    · simp [walkTrial, equal] at output
  | succ fuel ih =>
    obtain ⟨searchLength, restLength⟩ := G.walk_split_lengths alphabet n fuel length
    simp only [walkTrial] at output
    by_cases stop : y.length = n ∧ bits.head? = some true
    · rw [ite_eq_left stop] at output
      exact Or.inl ⟨(Option.some.inj output).symm, stop.1⟩
    · rw [ite_eq_right stop] at output
      cases search : G.inverseSearch alphabet n y ((bits.drop 1).take (G.searchSeed alphabet n)) with
      | none =>
        simp only [search] at output
        by_cases equal : y.length = n
        · rw [ite_eq_left equal] at output
          exact Or.inl ⟨(Option.some.inj output).symm, equal⟩
        · simp [equal] at output
      | some z =>
        simp only [search] at output
        have step := G.inverseSearch_sound ancestor searchLength search
        exact Or.inr ⟨z, step, ih (R.up_iff.mp step).1 restLength output⟩

theorem walkTrial_block (alphabet : List α) (n fuel : ℕ) (y : Word α)
    (bit : Bool) (searchBits rest : BitString) (length : searchBits.length = G.searchSeed alphabet n) :
    G.walkTrial alphabet n (fuel + 1) y (bit :: (searchBits ++ rest)) =
      if y.length = n ∧ bit = true then some y
      else match G.inverseSearch alphabet n y searchBits with
        | none => if y.length = n then some y else none
        | some z => G.walkTrial alphabet n fuel z rest := by
  simp [walkTrial, ← length, List.drop_append, Nat.add_comm]

theorem walkTrial_complete (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n fuel : ℕ} {y x : Word α} (ancestor : y ∈ R.ancestors n)
    (target : x ∈ R.walkOutputs n fuel y) :
    ∃ bits, bits.length = G.walkSeed alphabet n fuel ∧ G.walkTrial alphabet n fuel y bits = some x := by
  induction fuel generalizing y with
  | zero =>
    obtain ⟨rfl, equal⟩ := target
    exact ⟨[], by simp [walkSeed], by simp [walkTrial, equal]⟩
  | succ fuel ih =>
    rcases target with ⟨rfl, equal⟩ | ⟨z, step, target⟩
    · refine ⟨true :: List.replicate (G.walkSeed alphabet n (fuel + 1) - 1) false, ?_, ?_⟩
      · simp only [List.length_cons, List.length_replicate]
        have : 0 < G.walkSeed alphabet n (fuel + 1) := by unfold walkSeed; positivity
        omega
      · simp [walkTrial, equal]
    · obtain ⟨searchBits, searchLength, search⟩ := G.inverseSearch_complete alphabet complete ancestor step
      obtain ⟨rest, restLength, output⟩ := ih (R.up_iff.mp step).1 target
      refine ⟨false :: (searchBits ++ rest), ?_, ?_⟩
      · simp only [List.length_cons, List.length_append, searchLength, restLength, walkSeed]
        ring
      · rw [G.walkTrial_block alphabet n fuel y false searchBits rest searchLength]
        simpa [search] using output

/-- No full seed fails when the starting ancestor has enough remaining rank.
In particular, declining the stop coin cannot get stuck at a short word. -/
theorem walkTrial_total (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n fuel : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n)
    (enough : R.rankBound n ≤ R.rank y + fuel) {bits : BitString}
    (length : bits.length = G.walkSeed alphabet n fuel) :
    ∃ x, G.walkTrial alphabet n fuel y bits = some x := by
  induction fuel generalizing y bits with
  | zero =>
    obtain ⟨x, equal, size⟩ := R.walk_nonempty ancestor enough
    subst x
    exact ⟨y, by simp [walkTrial, size]⟩
  | succ fuel ih =>
    obtain ⟨searchLength, restLength⟩ := G.walk_split_lengths alphabet n fuel length
    simp only [walkTrial]
    by_cases stop : y.length = n ∧ bits.head? = some true
    · rw [ite_eq_left stop]
      exact ⟨y, rfl⟩
    · rw [ite_eq_right stop]
      cases search : G.inverseSearch alphabet n y ((bits.drop 1).take (G.searchSeed alphabet n)) with
      | none =>
        have equal : y.length = n := by
          by_contra different
          obtain ⟨z, success⟩ := G.inverseSearch_total alphabet complete ancestor
            (by have := R.ancestor_length_le ancestor; omega) searchLength
          rw [search] at success
          contradiction
        exact ⟨y, by simp [equal]⟩
      | some z =>
        have step := G.inverseSearch_sound ancestor searchLength search
        have increase := R.step_rank_lt (R.up_iff.mp step).2
        exact ih (R.up_iff.mp step).1 (by omega) restLength

theorem walkTrial_append (alphabet : List α) (n fuel : ℕ) (y : Word α)
    {bits : BitString} (length : bits.length = G.walkSeed alphabet n fuel) (extra : BitString) :
    G.walkTrial alphabet n fuel y (bits ++ extra) = G.walkTrial alphabet n fuel y bits := by
  induction fuel generalizing y bits with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨searchLength, restLength⟩ := G.walk_split_lengths alphabet n fuel length
    have enough : 1 + G.searchSeed alphabet n ≤ bits.length := by
      simp only [walkSeed, Nat.add_mul] at length
      omega
    have first : (bits ++ extra).head? = bits.head? := by
      cases bits with
      | nil => simp only [List.length_nil] at enough; omega
      | cons bit tail => rfl
    have search : ((bits ++ extra).drop 1).take (G.searchSeed alphabet n) =
        (bits.drop 1).take (G.searchSeed alphabet n) := by
      rw [List.drop_append_of_le_length (by omega : 1 ≤ bits.length)]
      exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)
    have rest : (bits ++ extra).drop (1 + G.searchSeed alphabet n) =
        bits.drop (1 + G.searchSeed alphabet n) ++ extra := List.drop_append_of_le_length enough
    rw [walkTrial, walkTrial, first, search, rest]
    by_cases stop : y.length = n ∧ bits.head? = some true
    · rw [ite_eq_left stop, ite_eq_left stop]
    · rw [ite_eq_right stop, ite_eq_right stop]
      cases G.inverseSearch alphabet n y ((bits.drop 1).take (G.searchSeed alphabet n)) with
      | none => rfl
      | some z => exact ih z restLength

end ComplexityOfGenerators.ExactRecursiveGenerators
