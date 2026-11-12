import ComplexityOfGenerators.Simulation.StarPaths.Model

namespace ComplexityOfGenerators.Simulation.StarPaths

set_option backward.isDefEq.respectTransparency false

/-- Every archived witness is a positive composition of the indicated sum,
and all its source indices have been certified. -/
theorem archive_sound (flags : List Bool) (n k : ℕ) (parts : Parts)
    (entry : (archive flags n)[k]? = some (some parts)) : Valid flags (n-k) parts := by
  induction n generalizing k parts with
  | zero =>
      cases k with
      | zero =>
          have empty : parts = [] := by simpa [archive] using entry.symm
          subst parts
          simp [Valid]
      | succ k => simp [archive] at entry
  | succ n ih =>
      cases k with
      | zero =>
          have result : scan flags (archive flags n) 1 none = some parts := by simpa [archive,stage] using entry
          obtain ⟨offset,previous,cell,available,equal⟩ := (scan_result flags _ 1 none parts result).resolve_left (by simp)
          have inside : offset < (archive flags n).length := (List.getElem?_eq_some_iff.mp cell).1
          rw [archive_length] at inside
          have prior := ih offset previous cell
          subst parts
          refine ⟨?_, ?_⟩
          · simp only [List.sum_cons]
            rw [prior.1]
            omega
          · intro j member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨by omega, by simpa [certified] using available⟩
            · exact prior.2 j member
      | succ k =>
          have prior : (archive flags n)[k]? = some (some parts) := by simpa [archive] using entry
          simpa only [Nat.add_sub_add_right] using ih k parts prior

private theorem archive_complete (flags : List Bool) (n : ℕ) :
    ∀ k, k ≤ n → (∃ parts, Valid flags k parts) →
      ((archive flags n)[n-k]?.bind id).isSome = true := by
  induction n with
  | zero =>
      intro k small witness
      have zero : k = 0 := by omega
      subst k
      simp [archive]
  | succ n ih =>
      intro k small witness
      by_cases last : k = n+1
      · subst k
        obtain ⟨parts,valid⟩ := witness
        cases parts with
        | nil => simp [Valid] at valid
        | cons j rest =>
          have positive : 0 < j := (valid.2 j (by simp)).1
          have available : (flags[j-1]?).getD false = true := (valid.2 j (by simp)).2
          have total : j+rest.sum = n+1 := by simpa using valid.1
          have restValid : Valid flags (n+1-j) rest := by
            refine ⟨by omega, ?_⟩
            intro q member
            exact valid.2 q (by simp [member])
          have prior := ih (n+1-j) (by omega) ⟨rest,restValid⟩
          have index : n-(n+1-j) = j-1 := by omega
          rw [index] at prior
          cases cell : (archive flags n)[j-1]? with
          | none => simp [cell] at prior
          | some value =>
              cases value with
              | none => simp [cell] at prior
              | some previous =>
                  simp only [archive,Nat.sub_self,List.getElem?_cons_zero,Option.bind_some,id_eq]
                  apply (scan_isSome flags _ 1 none).mpr
                  exact Or.inr ⟨j-1,previous,cell,available⟩
      · have smaller : k ≤ n := by omega
        have shift : n+1-k = (n-k)+1 := by omega
        simpa only [archive,shift,List.getElem?_cons_succ] using ih k smaller witness

private theorem archive_first (flags : List Bool) (n : ℕ) :
    (archive flags n)[0]? = some (fallback flags n) := by
  cases n <;> rfl

/-- The deterministic DP fallback exists exactly when some feasible positive
composition exists. It never reports a false certification. -/
theorem fallback_spec (flags : List Bool) (n : ℕ) :
    (∀ parts, fallback flags n = some parts → Valid flags n parts) ∧
      ((fallback flags n).isSome = true ↔ ∃ parts, Valid flags n parts) := by
  have sound (parts : Parts) (result : fallback flags n = some parts) : Valid flags n parts := by
    have cell : (archive flags n)[0]? = some (some parts) := by rw [archive_first,result]
    simpa only [Nat.sub_zero] using archive_sound flags n 0 parts cell
  refine ⟨sound, ?_⟩
  constructor
  · intro present
    obtain ⟨parts,result⟩ := Option.isSome_iff_exists.mp present
    exact ⟨parts,sound parts result⟩
  · intro witness
    have result := archive_complete flags n n le_rfl witness
    simpa only [Nat.sub_self,archive_first,Option.bind_some,id_eq] using result

theorem valid_length_le (flags : List Bool) (n : ℕ) (parts : Parts) (valid : Valid flags n parts) :
    parts.length ≤ n := by
  have positive : ∀ j ∈ parts, 0 < j := fun j member => (valid.2 j member).1
  rw [← valid.1]
  clear valid n
  induction parts with
  | nil => simp
  | cons j rest ih =>
      have first := positive j (by simp)
      have tail : ∀ q ∈ rest, 0 < q := fun q member => positive q (by simp [member])
      have bound := ih tail
      simp only [List.length_cons,List.sum_cons]
      omega

theorem payload_length (parts : Parts) : (payload parts).length = parts.sum+parts.length := by
  induction parts with
  | nil => rfl
  | cons j rest ih => simp [payload,ih]; omega

theorem valid_payload_bound (flags : List Bool) (n : ℕ) (parts : Parts) (valid : Valid flags n parts) :
    (payload parts).length ≤ 2*n := by
  rw [payload_length,valid.1]
  have := valid_length_le flags n parts valid
  omega

end ComplexityOfGenerators.Simulation.StarPaths
