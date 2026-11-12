import ComplexityOfGenerators.Simulation.StarPaths.Archive

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] readEntry capture consider stageBody

def flagSymbol : Bool → Symbol | false => .absent | true => .present
def flagsWord (flags : List Bool) : List Symbol := flags.map flagSymbol

@[simp] theorem flagsWord_available (flags : List Bool) :
    available (flagsWord flags).head? = (flags[0]?).getD false := by
  cases flags with
  | nil => rfl
  | cons flag rest => cases flag <;> rfl

/-- The current first-witness result and the two synchronized source cursors. -/
def StageRep (flags : List Bool) (entries : Table) (j : ℕ) (current : Option Parts) (s : Store) : Prop :=
  s 5 = encoded entries ∧ s 6 = flagsWord flags ∧ s 3 = List.replicate (j-1) .unit ∧
    s 10 = held current ∧ s 11 = flagWord current.isSome

private theorem consider_result {O : Type} (flag : Bool) (j : ℕ) (previous current : Option Parts) (s : Store)
    (counter : s 3 = List.replicate j .unit) (source : available (s 6).head? = flag)
    (previousWord : s 8 = held previous) (previousFlag : s 9 = flagWord previous.isSome)
    (currentWord : s 10 = held current) (currentFlag : s 11 = flagWord current.isSome) :
    (consider (O := O)).eval s 10 = held (offer current (candidate flag j previous)) ∧
      (consider (O := O)).eval s 11 = flagWord (offer current (candidate flag j previous)).isSome := by
  cases current <;> cases previous <;> cases flag <;>
    simp [consider,WordStack.Routine.branch,currentFlag,source,previousFlag,held,flagWord,
      WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.eval,currentWord,candidate,offer,
      capture_eval,counter,previousWord,payload]

theorem stageBody_represents {O : Type} (flags : List Bool) (previous : Option Parts) (rest : Table)
    (j : ℕ) (current : Option Parts) (s : Store) (positive : 0 < j)
    (represented : StageRep flags (previous::rest) j current s) :
    StageRep flags.tail rest (j+1) (offer current (candidate ((flags[0]?).getD false) j previous))
      ((stageBody (O := O)).eval s) := by
  rcases represented with ⟨cursor,source,counter,currentWord,currentFlag⟩
  let pushed := Function.update s 3 (.unit::s 3)
  let decoded := (readEntry (O := O)).eval pushed
  have decodedEq : decoded = Function.update (Function.update (Function.update
      (Function.update pushed 7 []) 8 (held previous)) 9 (flagWord previous.isSome)) 5 (encoded rest) := by
    apply readEntry_eval
    simpa [pushed,encoded] using cursor
  have decodedCounter : decoded 3 = List.replicate j .unit := by
    rw [decodedEq]
    change Symbol.unit::s 3 = List.replicate j Symbol.unit
    rw [counter]
    have index : j = (j-1)+1 := by omega
    conv_rhs => rw [index,List.replicate_succ]
  have decodedSource : available (decoded 6).head? = (flags[0]?).getD false := by
    rw [decodedEq]
    simpa [pushed,source] using flagsWord_available flags
  have decodedPrevious : decoded 8 = held previous := by rw [decodedEq]; simp
  have decodedFlag : decoded 9 = flagWord previous.isSome := by rw [decodedEq]; simp
  have decodedCurrent : decoded 10 = held current := by rw [decodedEq]; simpa [pushed] using currentWord
  have decodedCurrentFlag : decoded 11 = flagWord current.isSome := by rw [decodedEq]; simpa [pushed] using currentFlag
  have result := consider_result (O := O) _ j previous current decoded decodedCounter decodedSource
    decodedPrevious decodedFlag decodedCurrent decodedCurrentFlag
  have actual : (stageBody (O := O)).eval s =
      Function.update ((consider (O := O)).eval decoded) 6 (((consider (O := O)).eval decoded) 6).tail := by
    unfold stageBody
    rfl
  have fixed (index : Fin 35) (a : index ≠ 10) (b : index ≠ 11) (c : index ≠ 12) :
      (consider (O := O)).eval decoded index = decoded index := consider_frame index a b c decoded
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [actual]
    simp only [Function.update_of_ne (by decide : (5 : Fin 35) ≠ 6)]
    rw [fixed 5 (by decide) (by decide) (by decide),decodedEq]
    simp
  · rw [actual]
    change ((consider (O := O)).eval decoded 6).tail = flagsWord flags.tail
    rw [fixed 6 (by decide) (by decide) (by decide),decodedEq]
    simp [pushed,source,flagsWord,List.map_tail]
  · rw [actual]
    simp only [Function.update_of_ne (by decide : (3 : Fin 35) ≠ 6)]
    rw [fixed 3 (by decide) (by decide) (by decide),decodedCounter]
    simp
  · rw [actual]
    simpa using result.1
  · rw [actual]
    simpa using result.2

end ComplexityOfGenerators.Simulation.StarPaths
