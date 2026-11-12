import ComplexityOfGenerators.Simulation.StarPaths.Native

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true

@[simp] private theorem flagWord_present (available : Bool) : (flagWord available).head?.isSome = available := by
  cases available <;> rfl

/-- The native selector succeeds precisely for targets with a certified
positive composition; it succeeds on every cut block in that case. -/
theorem pathRoutine_success_iff {O : Type} (flags : List Bool) (bits : List Bool) (n : ℕ) (s : Store)
    (source : s 25 = flagsWord flags) (coins : s 17 = bits.map coinSymbol) (size : (s 22).length = n) :
    (((pathRoutine (O := O)).eval s 32).head?.isSome = true) ↔ ∃ parts, Valid flags n parts := by
  rw [(pathRoutine_value (O := O) flags bits n s source coins size).2,flagWord_present]
  exact selected_isSome flags n bits

/-- Every native successful path has the requested total and only certified
positive source indices. -/
theorem pathRoutine_sound {O : Type} (flags : List Bool) (bits : List Bool) (n : ℕ) (s : Store)
    (source : s 25 = flagsWord flags) (coins : s 17 = bits.map coinSymbol) (size : (s 22).length = n)
    (present : (((pathRoutine (O := O)).eval s 32).head?.isSome = true)) :
    ∃ parts, Valid flags n parts ∧ (pathRoutine (O := O)).eval s 31 = payload parts := by
  have value := pathRoutine_value (O := O) flags bits n s source coins size
  rw [value.2,flagWord_present] at present
  obtain ⟨parts,selectedEq⟩ := Option.isSome_iff_exists.mp present
  refine ⟨parts,selected_sound flags n bits parts selectedEq,?_⟩
  rw [value.1,selectedEq]
  rfl

/-- Each feasible composition has a fixed native witness block of exactly
n-1 cut coins. Every other caller stack may contain arbitrary data. -/
theorem pathRoutine_full_support {O : Type} (flags : List Bool) (n : ℕ) (parts : Parts) (s : Store)
    (source : s 25 = flagsWord flags) (size : (s 22).length = n) (valid : Valid flags n parts) :
    ∃ bits : List Bool, bits.length = n-1 ∧
      (pathRoutine (O := O)).eval (Function.update s 17 (bits.map coinSymbol)) 31 = payload parts ∧
      (pathRoutine (O := O)).eval (Function.update s 17 (bits.map coinSymbol)) 32 = [Symbol.present] := by
  obtain ⟨bits,length,selectedEq⟩ := selected_full_support flags n parts valid
  have actualSource : (Function.update s 17 (bits.map coinSymbol)) 25 = flagsWord flags := by simpa using source
  have actualSize : ((Function.update s 17 (bits.map coinSymbol)) 22).length = n := by simpa using size
  have value := pathRoutine_value (O := O) flags bits n (Function.update s 17 (bits.map coinSymbol))
    actualSource (by simp) actualSize
  refine ⟨bits,length,?_,?_⟩
  · rw [value.1,selectedEq]
    rfl
  · rw [value.2,selectedEq]
    rfl

/-- Zero uses the empty path and reports success independently of the cache. -/
theorem pathRoutine_zero {O : Type} (flags : List Bool) (bits : List Bool) (s : Store)
    (source : s 25 = flagsWord flags) (coins : s 17 = bits.map coinSymbol) (size : (s 22).length = 0) :
    (pathRoutine (O := O)).eval s 31 = [] ∧ (pathRoutine (O := O)).eval s 32 = [Symbol.present] := by
  have value := pathRoutine_value (O := O) flags bits 0 s source coins size
  simpa only [selected_zero,held,payload,List.flatMap_nil,Option.isSome_some,flagWord,ite_true] using value

end ComplexityOfGenerators.Simulation.StarPaths
