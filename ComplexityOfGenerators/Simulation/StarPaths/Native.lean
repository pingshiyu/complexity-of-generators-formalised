import ComplexityOfGenerators.Simulation.StarPaths.Frames

/-! A genuine finite stack path selector: dynamic programming computes a
fallback, a bounded cut-coin proposal supplies full support, and a native
validation scan selects the proposal or fallback without rejection. -/
namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] dpRoutine proposalRoutine validationRoutine

def saveFallback {O : Type} : Step O :=
  (WordStack.Routine.assign 10 14 12 (by decide) (by decide) (by decide) id).seq
    (WordStack.Routine.assign 11 15 12 (by decide) (by decide) (by decide) id)

def selectResult {O : Type} : Step O := WordStack.Routine.branch 20 fun valid => if valid.isSome then
  (WordStack.Routine.clear 32).seq (WordStack.Routine.ofLocal (Local.push 32 .present))
  else (WordStack.Routine.assign 14 31 12 (by decide) (by decide) (by decide) id).seq
    (WordStack.Routine.assign 15 32 12 (by decide) (by decide) (by decide) id)

def pathRoutine {O : Type} : Step O := dpRoutine.seq
  (saveFallback.seq (proposalRoutine.seq (validationRoutine.seq selectResult)))

theorem saveFallback_fields {O : Type} (s : Store) :
    (saveFallback (O := O)).eval s 14 = s 10 ∧ (saveFallback (O := O)).eval s 15 = s 11 := by
  simp [saveFallback,WordStack.Routine.seq,WordStack.Routine.assign_eval]

theorem saveFallback_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 14) (c : j ≠ 15) :
    (saveFallback (O := O)).Fixes j := by
  intro s
  simp [saveFallback,WordStack.Routine.seq,WordStack.Routine.assign_eval,a,b,c]

theorem selectResult_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 31) (c : j ≠ 32) :
    (selectResult (O := O)).Fixes j := by
  unfold selectResult
  apply WordStack.Routine.Fixes.branch
  intro valid
  split_ifs
  · exact (WordStack.Routine.fixes_clear 32 j c).seq (WordStack.Routine.fixes_push 32 j Symbol.present c)
  · exact (WordStack.Routine.fixes_assign 14 31 12 (by decide) (by decide) (by decide) id j b a).seq
      (WordStack.Routine.fixes_assign 15 32 12 (by decide) (by decide) (by decide) id j c a)

private theorem selectResult_fields {O : Type} (parts : Parts) (fallback : Option Parts) (valid : Bool) (s : Store)
    (proposalWord : s 31 = payload parts) (savedWord : s 14 = held fallback)
    (savedFlag : s 15 = flagWord fallback.isSome) (checked : s 20 = flagWord valid) :
    (selectResult (O := O)).eval s 31 = held (if valid then some parts else fallback) ∧
      (selectResult (O := O)).eval s 32 = flagWord (if valid then some parts else fallback).isSome := by
  cases valid <;> simp [selectResult,WordStack.Routine.branch,checked,flagWord,WordStack.Routine.seq,
    WordStack.Routine.clear,WordStack.Routine.ofLocal,Local.eval_push,WordStack.Routine.assign_eval,
    savedWord,savedFlag,proposalWord,held]

private theorem positive_length_le_sum (parts : Parts) (positive : ∀ j ∈ parts, 0 < j) :
    parts.length ≤ parts.sum := by
  induction parts with
  | nil => simp
  | cons j rest ih =>
      have first := positive j (by simp)
      have tail := ih (fun k member => positive k (by simp [member]))
      simp only [List.length_cons,List.sum_cons]
      omega

/-- Exact executable semantics of the bounded native path selector. Registers
22/25 contain the master unary length and certified availability vector; 17
contains the supplied cut coins. Results occupy 31/32. -/
theorem pathRoutine_value {O : Type} (flags : List Bool) (bits : List Bool) (n : ℕ) (s : Store)
    (source : s 25 = flagsWord flags) (coins : s 17 = bits.map coinSymbol) (size : (s 22).length = n) :
    (pathRoutine (O := O)).eval s 31 = held (selected flags n bits) ∧
      (pathRoutine (O := O)).eval s 32 = flagWord (selected flags n bits).isSome := by
  let dynamic := (dpRoutine (O := O)).eval s
  let cached := (saveFallback (O := O)).eval dynamic
  let proposed := (proposalRoutine (O := O)).eval cached
  let checked := (validationRoutine (O := O)).eval proposed
  have dynamicResult : dynamic 10 = held (fallback flags n) ∧ dynamic 11 = flagWord (fallback flags n).isSome := by
    simpa only [size] using dpRoutine_result (O := O) flags s source
  have dynamicMaster (j : Fin 35) (master : j = 17 ∨ j = 22 ∨ j = 25) : dynamic j = s j := dpRoutine_frame j master s
  have cachedSaved : cached 14 = held (fallback flags n) ∧ cached 15 = flagWord (fallback flags n).isSome := by
    have fields := saveFallback_fields (O := O) dynamic
    exact ⟨fields.1.trans dynamicResult.1,fields.2.trans dynamicResult.2⟩
  have cachedMaster (j : Fin 35) (master : j = 17 ∨ j = 22 ∨ j = 25) : cached j = s j := by
    have a : j ≠ 12 := by rcases master with rfl | rfl | rfl <;> decide
    have b : j ≠ 14 := by rcases master with rfl | rfl | rfl <;> decide
    have c : j ≠ 15 := by rcases master with rfl | rfl | rfl <;> decide
    exact (saveFallback_frame j a b c dynamic).trans (dynamicMaster j master)
  have cachedSize : (cached 22).length = n := by rw [cachedMaster 22 (by simp),size]
  have cachedCoins : cached 17 = bits.map coinSymbol := (cachedMaster 17 (by simp)).trans coins
  have proposalResult := proposalRoutine_value (O := O) cached n bits cachedSize cachedCoins
  have proposedMaster : proposed 22 = cached 22 := proposalRoutine_frame 22 (by decide) (by decide) (by decide) (by decide) cached
  have proposedSize : (proposed 22).length = n := by rw [proposedMaster,cachedSize]
  have proposedSource : proposed 25 = flagsWord flags :=
    (proposalRoutine_frame 25 (by decide) (by decide) (by decide) (by decide) cached).trans
      ((cachedMaster 25 (by simp)).trans source)
  have positive := proposal_positive n bits
  have enough : (proposal n bits).length ≤ (proposed 22).length := by
    rw [proposedSize]
    exact (positive_length_le_sum _ positive).trans_eq (proposal_sum n bits)
  have validationResult := validationRoutine_value (O := O) flags (proposal n bits) proposed positive enough proposalResult.1 proposedSource
  have checkedWord : checked 31 = payload (proposal n bits) :=
    (validationRoutine_frame 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) proposed).trans proposalResult.1
  have checkedSavedWord : checked 14 = held (fallback flags n) :=
    (validationRoutine_frame 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) proposed).trans
      ((proposalRoutine_frame 14 (by decide) (by decide) (by decide) (by decide) cached).trans cachedSaved.1)
  have checkedSavedFlag : checked 15 = flagWord (fallback flags n).isSome :=
    (validationRoutine_frame 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) proposed).trans
      ((proposalRoutine_frame 15 (by decide) (by decide) (by decide) (by decide) cached).trans cachedSaved.2)
  have result := selectResult_fields (O := O) (proposal n bits) (fallback flags n) (allowed flags (proposal n bits))
    checked checkedWord checkedSavedWord checkedSavedFlag validationResult
  have actual : (pathRoutine (O := O)).eval s = (selectResult (O := O)).eval checked := by unfold pathRoutine; rfl
  rw [actual]
  exact result

/-- Neither the master unary length nor the certification cache is mutated. -/
theorem pathRoutine_frame {O : Type} (j : Fin 35) (master : j = 22 ∨ j = 25) :
    (pathRoutine (O := O)).Fixes j := by
  have a : j ≠ 12 := by rcases master with rfl | rfl <;> decide
  have b : j ≠ 14 := by rcases master with rfl | rfl <;> decide
  have c : j ≠ 15 := by rcases master with rfl | rfl <;> decide
  have d : j ≠ 16 := by rcases master with rfl | rfl <;> decide
  have e : j ≠ 17 := by rcases master with rfl | rfl <;> decide
  have f : j ≠ 18 := by rcases master with rfl | rfl <;> decide
  have g : j ≠ 19 := by rcases master with rfl | rfl <;> decide
  have h : j ≠ 20 := by rcases master with rfl | rfl <;> decide
  have i : j ≠ 21 := by rcases master with rfl | rfl <;> decide
  have k : j ≠ 23 := by rcases master with rfl | rfl <;> decide
  have l : j ≠ 31 := by rcases master with rfl | rfl <;> decide
  have m : j ≠ 32 := by rcases master with rfl | rfl <;> decide
  unfold pathRoutine
  exact (dpRoutine_frame j (master.elim (fun x => Or.inr (Or.inl x)) (fun x => Or.inr (Or.inr x)))).seq
    ((saveFallback_frame j a b c).seq ((proposalRoutine_frame j a e f l).seq
      ((validationRoutine_frame j a d f g h i k).seq (selectResult_frame j a l m))))

end ComplexityOfGenerators.Simulation.StarPaths
