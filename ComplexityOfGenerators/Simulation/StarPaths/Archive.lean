import ComplexityOfGenerators.Simulation.StarPaths.Basic

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
attribute [local irreducible] readEntry capture

private theorem payload_members (parts : Parts) : ∀ a ∈ payload parts, isPayload a = true := by
  intro a member
  obtain ⟨j,_,member⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · have equal : a = Symbol.unit := (List.mem_replicate.mp member).2
    subst a
    rfl

private theorem takeWhile_prefix (word rest : List Symbol) (valid : ∀ a ∈ word, isPayload a = true) :
    (word++rest).takeWhile isPayload = word++rest.takeWhile isPayload := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have first := valid a (by simp)
      have tail : ∀ b ∈ word, isPayload b = true := fun b member => valid b (by simp [member])
      simp [List.takeWhile_cons,first,ih tail]

private theorem dropWhile_prefix (word rest : List Symbol) (valid : ∀ a ∈ word, isPayload a = true) :
    (word++rest).dropWhile isPayload = rest.dropWhile isPayload := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      have first := valid a (by simp)
      have tail : ∀ b ∈ word, isPayload b = true := fun b member => valid b (by simp [member])
      simp [List.dropWhile_cons,first,ih tail]

private theorem encoded_stops (entries : Table) :
    (encoded entries).takeWhile isPayload = [] ∧ (encoded entries).dropWhile isPayload = encoded entries := by
  cases entries with
  | nil => simp [encoded]
  | cons value rest => cases value <;> simp [encoded,entry,isPayload]

/-- This is the actual native decoder for one tagged DP entry. -/
theorem readEntry_eval {O : Type} (value : Option Parts) (rest : Table) (s : Store)
    (cursor : s 5 = entry value ++ encoded rest) :
    (readEntry (O := O)).eval s = Function.update (Function.update (Function.update
      (Function.update s 7 []) 8 (held value)) 9 (flagWord value.isSome)) 5 (encoded rest) := by
  have stop := encoded_stops rest
  have taken := takeWhile_prefix (payload (value.getD [])) (encoded rest) (payload_members _)
  have dropped := dropWhile_prefix (payload (value.getD [])) (encoded rest) (payload_members _)
  cases value <;> simp only [Option.getD_some,Option.getD_none] at taken dropped <;> funext j <;>
    by_cases a : j = 5 <;> by_cases b : j = 7 <;> by_cases c : j = 8 <;> by_cases d : j = 9 <;>
    simp [readEntry,WordStack.Routine.seq,WordStack.Routine.clear,WordStack.Routine.branch,
      WordStack.Routine.ofLocal,WordStack.Routine.skip,Local.eval_pop,Local.eval_push,
      WordStack.Routine.transferWhile,WordStack.Routine.transfer,entry,available,held,flagWord,
      cursor,stop.1,stop.2,taken,dropped,a,b,c,d]

theorem capture_eval {O : Type} (s : Store) :
    (capture (O := O)).eval s = Function.update (Function.update (Function.update s 12 [])
      10 (.cut::List.replicate (s 3).length .unit++s 8)) 11 (.present::s 11) := by
  simp only [capture,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.copy,
    WordStack.Routine.ofLocal,Local.eval_push]
  funext j
  by_cases a : j = 12 <;> by_cases b : j = 10 <;> by_cases c : j = 11 <;>
    simp [a,b,c,List.map_const']

end ComplexityOfGenerators.Simulation.StarPaths
