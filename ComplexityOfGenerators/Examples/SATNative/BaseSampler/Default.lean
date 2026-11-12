import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Check
import ComplexityOfGenerators.Examples.SATBaseDefaultNative
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

def defaultSlots : Fin 2 ↪ Fin 35 :=
  ⟨fun j => if j = 0 then 32 else 33, by
    intro a b same
    fin_cases a <;> fin_cases b <;> simp_all⟩

def defaultClassify : Routine Symbol Symbol 35 :=
  (Routine.clear 34).seq ((BaseDefaultNative.classify 0 4).rename defaultSlots)

def defaultLong : Routine Symbol Symbol 35 :=
  (Routine.ofLocal (Local.push 34 .closeClause)).seq
    ((Routine.transfer 32 34 (by decide) (fun _ => .trueConstant)).seq
      (Routine.ofLocal ((Local.push 34 .openClause).seq
        ((Local.push 34 .separator).seq (Local.push 34 .separator)))))

def defaultFill : Routine Symbol Symbol 35 :=
  Routine.branch 33 fun head => match head with
  | some .one => Routine.ofLocal ((Local.push 34 .separator).seq (Local.push 34 .separator))
  | some .positive => Routine.ofLocal ((Local.push 34 .separator).seq
      ((Local.push 34 .zero).seq ((Local.push 34 .separator).seq (Local.push 34 .one))))
  | some .separator => defaultLong
  | _ => Routine.skip

def defaultRoutine : Routine Symbol Symbol 35 := defaultClassify.seq defaultFill

theorem defaultClassify_fields (s : Store) (n : ℕ)
    (counter : s 32 = List.replicate n .zero) (empty : s 33 = []) :
    defaultClassify.eval s 32 = List.replicate (n-4) .zero ∧
      defaultClassify.eval s 33 = BaseDefaultNative.flag n ∧ defaultClassify.eval s 34 = [] := by
  have projected : ((Routine.clear (O := Symbol) 34).eval s) ∘ defaultSlots = BaseDefaultNative.loadedStore n := by
    funext j
    fin_cases j <;> simp [defaultSlots, Routine.clear, counter, empty, BaseDefaultNative.loadedStore]
  have result := BaseDefaultNative.classify_eval n
  constructor
  · change (((BaseDefaultNative.classify 0 4).rename defaultSlots).eval _) (defaultSlots 0) = _
    rw [Routine.rename_eval_here, projected, result]
    simp [BaseDefaultNative.classifiedStore]
  constructor
  · change (((BaseDefaultNative.classify 0 4).rename defaultSlots).eval _) (defaultSlots 1) = _
    rw [Routine.rename_eval_here, projected, result]
    simp [BaseDefaultNative.classifiedStore]
  · have frame := Routine.rename_eval_frame (BaseDefaultNative.classify 0 4) defaultSlots
      ((Routine.clear (O := Symbol) 34).eval s) 34 (by intro j; fin_cases j <;> decide)
    simpa [defaultClassify, Routine.seq, Routine.clear] using frame

theorem defaultRoutine_value (s : Store) (n : ℕ)
    (counter : s 32 = List.replicate n .zero) (empty : s 33 = [])
    (productive : BaseProductive n) : defaultRoutine.eval s 34 = baseDefault n := by
  have fields := defaultClassify_fields s n counter empty
  change defaultFill.eval (defaultClassify.eval s) 34 = _
  by_cases two : n = 2
  · subst n
    simp [defaultFill, Routine.branch, fields.2.1, BaseDefaultNative.flag,
      Routine.ofLocal, Local.eval, Local.push, Action.apply, fields.2.2, baseDefault, Formula.encode]
  · by_cases four : n = 4
    · subst n
      simp [defaultFill, Routine.branch, fields.2.1, BaseDefaultNative.flag,
        Routine.ofLocal, Local.eval, Local.push, Action.apply, fields.2.2, baseDefault, Formula.encode]
    · have large : 5 ≤ n := by rcases productive with ⟨_, _⟩; omega
      simp [defaultFill, Routine.branch, fields.2.1, BaseDefaultNative.flag, two, four, large,
        defaultLong, Routine.seq, Routine.ofLocal, Local.eval, Local.push, Routine.transfer,
        fields.1, fields.2.2, Action.apply, baseDefault_long n large]

theorem defaultRoutine_flag (s : Store) (n : ℕ)
    (counter : s 32 = List.replicate n .zero) (empty : s 33 = []) :
    (defaultRoutine.eval s 33).head?.isSome = decide (BaseProductive n) := by
  have fields := defaultClassify_fields s n counter empty
  have frame : defaultFill.Fixes 33 := by
    intro store
    cases head : (store 33).head? with
    | none => simp [defaultFill, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
    | some symbol => cases symbol <;>
        simp [defaultFill, Routine.branch, head, defaultLong, Routine.seq, Routine.ofLocal,
          Local.eval, Local.push, Routine.transfer, Routine.skip, Action.apply]
  rw [defaultRoutine, Routine.seq, frame, fields.2.1]
  rcases n with _ | _ | _ | _ | _ | n <;> simp [BaseDefaultNative.flag, BaseProductive]

theorem defaultRoutine_cost (s : Store) (n : ℕ)
    (counter : s 32 = List.replicate n .zero) (empty : s 33 = []) (proposal : (s 34).length ≤ n) :
    defaultRoutine.cost s ≤ 20 * n + 40 := by
  have classifier := BaseDefaultNative.classify_cost 0 4 (((Routine.clear (O := Symbol) 34).eval s) ∘ defaultSlots)
  have fields := defaultClassify_fields s n counter empty
  have fill : defaultFill.cost (defaultClassify.eval s) ≤ 6 * n + 20 := by
    simp only [defaultFill, Routine.branch]
    cases head : (defaultClassify.eval s 33).head? with
    | none => simp [Routine.skip, Routine.ofLocal, Local.ticks]
    | some symbol => cases symbol <;>
        simp [Routine.skip, Routine.ofLocal, Local.ticks, Local.push, Local.eval, defaultLong,
          Routine.seq, Routine.transfer, fields.1, fields.2.2, Action.apply] <;> omega
  change 3 * (s 34).length + 1 +
    ((BaseDefaultNative.classify 0 4).rename defaultSlots).cost ((Routine.clear (O := Symbol) 34).eval s) + 1 +
      defaultFill.cost (defaultClassify.eval s) ≤ _
  rw [Routine.rename_cost]
  omega

end
end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
