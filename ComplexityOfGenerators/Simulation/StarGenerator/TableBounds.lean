import ComplexityOfGenerators.Simulation.StarGenerator.Table
import ComplexityOfGenerators.Proofs.PolynomialStarSupport
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem entry_length (value : Option (List α)) :
    (entry G value).length = 1 + (UnionGenerator.held G G value).length := by
  cases value <;> simp [entry, UnionGenerator.held, UnionGenerator.letters, Nat.add_comm]

theorem encoded_length_bound (entries : Table α) (limit : ℕ)
    (sizes : ∀ value ∈ entries, (entry G value).length ≤ limit) :
    (encoded G entries).length ≤ entries.length * limit := by
  induction entries with
  | nil => simp [encoded]
  | cons value rest ih =>
    have first := sizes value (by simp)
    have tail := ih (by intro v hv; exact sizes v (by simp [hv]))
    simp only [encoded, List.flatMap_cons, List.length_append, List.length_cons] at *
    nlinarith

theorem sized_entry_bound (table : Table α) (sized : Sized table) (value : Option (List α))
    (member : value ∈ table) : (entry G value).length ≤ table.length := by
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
  have inside : i < table.length := List.getElem?_eq_some_iff.mp lookup |>.1
  cases value with
  | none => simpa [entry] using (by omega : 1 ≤ table.length)
  | some word =>
    have length := sized i word (by rw [lookup]; rfl)
    simp [entry, UnionGenerator.letters, length]
    omega

theorem archive_length_bound (table : Table α) (sized : Sized table) :
    (archive G table).length ≤ table.length ^ 2 := by
  have bound := encoded_length_bound G table.reverse table.length
    (by intro value member; exact sized_entry_bound G table sized value (List.mem_reverse.mp member))
  simpa [archive, pow_two] using bound

theorem archive_length_le (table : Table α) (sized : Sized table) (n : ℕ) (length : table.length ≤ n + 1) :
    (archive G table).length ≤ (n + 1) ^ 2 :=
  (archive_length_bound G table sized).trans (Nat.pow_le_pow_left length 2)

/-- Reading a table cursor only stores a bounded prefixSize of the remaining entry. -/
theorem readEntry_raw (s : Store G) :
    (readEntry G).eval s = Function.update (Function.update (Function.update
      (Function.update s 25 []) 26 ((s 34).tail.takeWhile (isLetter G)))
      28 (UnionGenerator.flagWord G G (available G (s 34).head?)))
      34 ((s 34).tail.dropWhile (isLetter G)) := by
  funext j
  fin_cases j <;>
    simp [readEntry, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.branch,
      UnionGenerator.flag_eval, WordStack.Routine.ofLocal, Local.eval_pop,
      WordStack.Routine.transferWhile, WordStack.Routine.transfer, List.map_id,
      List.reverse_reverse]

theorem readEntry_bound (s : Store G) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((readEntry G).eval s) cap ∧ (readEntry G).cost s ≤ 40 * (cap + 1) := by
  have tail : (s 34).tail.length ≤ cap := by
    have := sizes 34
    simp only [List.length_tail]
    omega
  have prefixSize : ((s 34).tail.takeWhile (isLetter G)).length ≤ cap :=
    (List.takeWhile_prefix (l := (s 34).tail) (isLetter G)).length_le.trans tail
  have suffix : ((s 34).tail.dropWhile (isLetter G)).length ≤ cap :=
    (List.dropWhile_suffix (l := (s 34).tail) (isLetter G)).length_le.trans tail
  constructor
  · rw [readEntry_raw]
    apply (((sizes.clear 25).update 26 _ prefixSize).update 28 _ ?_).update 34 _ suffix
    cases available G (s 34).head? <;> simp_all [UnionGenerator.flagWord]
  · have h25 := sizes 25
    have h26 := sizes 26
    have h28 := sizes 28
    cases equal : available G (s 34).head? <;>
      simp [readEntry, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.branch,
        UnionGenerator.flag, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.pop, Local.push, Local.ticks, Local.eval, Action.apply,
        Local.eval_pop, Local.eval_push, WordStack.Routine.transferWhile, WordStack.Routine.transfer, equal] <;> omega

/-- Appending preserves every store except the archive and cleared scratch. -/
theorem appendEntry_bound (s : Store G) (cap : ℕ) (sizes : StoreBound s cap) (positive : 1 ≤ cap)
    (value : Option (List α)) (space : (entry G value ++ s 29).length ≤ cap)
    (word : s 31 = UnionGenerator.held G G value)
    (found : s 32 = UnionGenerator.flagWord G G value.isSome) :
    StoreBound ((appendEntry G).eval s) cap ∧ (appendEntry G).cost s ≤ 30 * (cap + 1) := by
  constructor
  · intro j
    by_cases archive : j = 29
    · subst j
      rw [appendEntry_archive G value s word found]
      exact space
    · by_cases scratch : j = 33
      · subst j
        cases value <;> simp [appendEntry, WordStack.Routine.branch, found, UnionGenerator.flagWord,
          WordStack.Routine.seq, WordStack.Routine.copy, WordStack.Routine.ofLocal, Local.eval_push,
          Function.update_apply] <;> exact sizes 33
      · rw [appendEntry_fixes G j archive scratch]
        exact sizes j
  · have h31 := sizes 31
    have h33 := sizes 33
    cases value <;>
      simp [appendEntry, WordStack.Routine.branch, found, UnionGenerator.flagWord,
        WordStack.Routine.seq, WordStack.Routine.copy, WordStack.Routine.ofLocal, Local.push, Local.ticks] <;> omega


theorem bounded_entry_length (table : Table α) (n bound : ℕ) (bounded : BoundedAt n bound table)
    (length : table.length ≤ n + 1) (value : Option (List α)) (member : value ∈ table) :
    (entry G value).length ≤ n * bound + 1 := by
  cases value with
  | none => simp [entry]
  | some word =>
    obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
    have inside : i < table.length := List.getElem?_eq_some_iff.mp lookup |>.1
    have wordLength := bounded i word (by rw [lookup]; rfl) (by omega)
    have index : i * bound ≤ n * bound := Nat.mul_le_mul_right _ (by omega)
    simp only [entry, List.length_cons, UnionGenerator.letters, List.length_map]
    omega

theorem archive_length_bounded (table : Table α) (n bound : ℕ) (bounded : BoundedAt n bound table)
    (length : table.length ≤ n + 1) :
    (archive G table).length ≤ (n + 1) * (n * bound + 1) := by
  have encodedBound := encoded_length_bound G table.reverse (n * bound + 1)
    (by intro value member; exact bounded_entry_length G table n bound bounded length value (List.mem_reverse.mp member))
  have archiveBound : (archive G table).length ≤ table.length * (n * bound + 1) := by
    simpa [archive] using encodedBound
  exact archiveBound.trans (Nat.mul_le_mul_right _ length)

end
end ComplexityOfGenerators.Simulation.StarGenerator
