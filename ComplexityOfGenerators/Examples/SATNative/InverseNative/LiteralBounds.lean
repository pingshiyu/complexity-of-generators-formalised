import ComplexityOfGenerators.Examples.SATNative.InverseNative.Literal
import ComplexityOfGenerators.Examples.SATNative.SubstitutionEmitBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack NativeBody

set_option backward.isDefEq.respectTransparency false

theorem freshLiteral_bound {O : Type} (value bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (fresh : (s 10).length + 1 ≤ budget) :
    stackBound budget ((freshLiteral (O := O) value bit).eval s) := by
  intro j
  have tagBound := sizes 11
  by_cases a : j = 5 <;> by_cases b : j = 9 <;> by_cases c : j = 11 <;>
    simp [freshLiteral, Routine.seq, Routine.assign_eval, Routine.ofLocal, Local.eval_push,
      Local.eval_write, a, b, c, List.length_tail] <;> first | exact sizes _ | omega

theorem freshLiteral_cost {O : Type} (value bit : Bool) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (freshLiteral (O := O) value bit).cost s ≤ 20 * (budget + 1) := by
  have index := sizes 5
  have scratch := sizes 9
  have count := sizes 10
  simp only [freshLiteral, Routine.seq, Routine.assign_cost, Routine.ofLocal,
    Local.write, Local.pop, Local.push, Local.ticks]
  omega

theorem rewriteLiteral_bound {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (fresh : (s 10).length + 1 ≤ budget) :
    stackBound budget ((rewriteLiteral (O := O) bit).eval s) := by
  by_cases choose : (s 31).head? = some .one
  · cases tag : (s 11).head? with
    | none => simpa [rewriteLiteral, Routine.branch, choose, tag, Routine.skip, Routine.ofLocal, Local.eval] using sizes
    | some symbol =>
      cases symbol <;> simp only [rewriteLiteral, Routine.branch, choose, ite_true, tag]
      all_goals first | exact sizes | exact freshLiteral_bound _ bit s budget positive sizes fresh
  · simpa [rewriteLiteral, Routine.branch, choose, Routine.skip, Routine.ofLocal, Local.eval] using sizes

theorem rewriteLiteral_cost {O : Type} (bit : Bool) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (rewriteLiteral (O := O) bit).cost s ≤ 25 * (budget + 1) := by
  have yes := freshLiteral_cost (O := O) true bit s budget sizes
  have no := freshLiteral_cost (O := O) false bit s budget sizes
  by_cases choose : (s 31).head? = some .one
  · cases tag : (s 11).head? with
    | none => simp [rewriteLiteral, Routine.branch, choose, tag, Routine.skip, Routine.ofLocal, Local.ticks] <;> omega
    | some symbol => cases symbol <;>
        simp [rewriteLiteral, Routine.branch, choose, tag, Routine.skip, Routine.ofLocal, Local.ticks] <;> omega
  · simp [rewriteLiteral, Routine.branch, choose, Routine.skip, Routine.ofLocal, Local.ticks] <;> omega

theorem rewriteLiteral_index_within {O : Type} (bit : Bool) (s : Store)
    (old : (s 5).length ≤ (s 4).length) (fresh : (s 10).length + 1 ≤ (s 4).length) :
    ((rewriteLiteral (O := O) bit).eval s 5).length ≤ (s 4).length := by
  by_cases choose : (s 31).head? = some .one
  · cases tag : (s 11).head? with
    | none => simpa [rewriteLiteral, Routine.branch, choose, tag, Routine.skip, Routine.ofLocal, Local.eval] using old
    | some symbol => cases symbol <;>
        simp [rewriteLiteral, Routine.branch, choose, tag, freshLiteral, Routine.seq, Routine.assign_eval,
          Routine.ofLocal, Routine.skip, Local.eval_push, Local.eval_write, Local.eval] <;> omega
  · simpa [rewriteLiteral, Routine.branch, choose, Routine.skip, Routine.ofLocal, Local.eval] using old

theorem liftLiteral_bound {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s)
    (old : (s 5).length ≤ (s 4).length) (fresh : (s 10).length + 1 ≤ (s 4).length) :
    stackBound (budget + (s 4).length + 1) ((liftLiteral (O := O) bit).eval s) := by
  let rewritten := (rewriteLiteral (O := O) bit).eval s
  let emitted := (NativeSubstitution.emitLiteral (O := O)).eval rewritten
  have first := rewriteLiteral_bound (O := O) bit s budget positive sizes (fresh.trans (sizes 4))
  have cap : rewritten 4 = s 4 := rewriteLiteral_frame (O := O) bit s 4 (by decide) (by decide) (by decide)
  have within : (rewritten 5).length ≤ (rewritten 4).length := by rw [cap]; exact rewriteLiteral_index_within bit s old fresh
  have last := NativeSubstitution.emitLiteral_bound (O := O) rewritten budget first within
  rw [cap] at last
  change StoreBound (Function.update emitted 31 (emitted 31).tail) (budget + (s 4).length + 1)
  exact StoreBound.update last 31 _ (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (last 31))

theorem liftLiteral_cost {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (fresh : (s 10).length + 1 ≤ budget) :
    (liftLiteral (O := O) bit).cost s ≤ 200 * (budget + 1) := by
  have first := rewriteLiteral_cost (O := O) bit s budget sizes
  have after := rewriteLiteral_bound (O := O) bit s budget positive sizes fresh
  have emitted := NativeSubstitution.emitLiteral_cost (O := O) ((rewriteLiteral (O := O) bit).eval s) budget after
  change (rewriteLiteral (O := O) bit).cost s + 1 +
    ((NativeSubstitution.emitLiteral (O := O)).cost ((rewriteLiteral (O := O) bit).eval s) + 1 + 1) ≤ _
  omega

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
