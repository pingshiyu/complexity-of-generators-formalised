import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.More
import ComplexityOfGenerators.Examples.SATNative.InverseNative.Value

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] InverseNative.bodyTransform transform

theorem clearedLabel_represents (capacity active : ℕ) (state : NativeBody.State) (m : Memory)
    (represented : Represents capacity active state m.store) :
    Represents capacity active state (m.set 3 []).store := by
  simpa [Represents,NativeBody.Represents,Function.comp_def,Memory.set,slots,BaseSampler.verifierSlots] using represented

theorem chooseBit_singleton (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (counter : m.store 32 = List.replicate n .zero)
    (represented : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ m.store)
    (clock : NativeBody.tokenCount formula ≤ (m.store 16).length)
    (random : m.randomHead = 0) (output : m.output = []) (label : m.store 3 = [bitSymbol bit]) :
    ∃ ticks ≤ moreBitBudget bit n bits (m.set 3 [])+3, ∃ result,
      (chooseBit bit).Runs n bits m ticks result ∧ result.outcome = bitOutcome bit capacity active formula n bits := by
  have first := Command.pop_runs (3 : Fin 35) bits m index
  rw [label,List.tail_cons] at first
  have rep := clearedLabel_represents capacity active _ m represented
  have count : (m.set 3 []).store 32 = List.replicate n .zero := by simpa using counter
  have enough : NativeBody.tokenCount formula ≤ ((m.set 3 []).store 16).length := by simpa using clock
  obtain ⟨lastTicks,lastCost,result,lastRun,outcome⟩ := moreBit_runs bit bound formula valid n bits (m.set 3 []) index count rep enough random output
  have branch : (Command.branch 3 fun tail => if tail.1.isSome then .drain else moreBit bit).Runs n bits (m.set 3 []) (1+lastTicks) result := by
    apply Command.Runs.branch
    simpa [observe] using lastRun
  have run := Command.Runs.seq _ _ _ _ 1 (1+lastTicks) result first branch
  exact ⟨1+1+(1+lastTicks),by omega,result,run,outcome⟩

theorem chooseBit_bad_tail (bit : Bool) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (random : m.randomHead = 0)
    (first second : Symbol) (rest : List Symbol) (label : m.store 3 = first :: second :: rest) :
    (chooseBit bit).Runs n bits m (3+bits.length) .exhausted := by
  have pop := Command.pop_runs (3 : Fin 35) bits m index
  rw [label,List.tail_cons] at pop
  let ready := m.set 3 (second :: rest)
  have drain : Command.drain.Runs n bits ready bits.length .exhausted := by
    simpa only [ready,Memory.set_random,random,Nat.sub_zero] using Command.Runs.drain (n := n) (bits := bits) ready
  have branch : (Command.branch 3 fun tail => if tail.1.isSome then .drain else moreBit bit).Runs
      n bits ready (1+bits.length) .exhausted := by
    apply Command.Runs.branch
    simpa [observe,ready] using drain
  have run := Command.Runs.seq _ _ _ _ 1 (1+bits.length) .exhausted pop branch
  convert run using 1 <;> first | rfl | omega

def labelBudget (n : ℕ) (bits : BitString) (m : Memory) : ℕ :=
  moreBitBudget false n bits (m.set 3 [])+moreBitBudget true n bits (m.set 3 [])+
    4*(m.store 34).length+bits.length+10

def labelOutcome (capacity active : ℕ) (formula : Formula) (n : ℕ) (target label : List Symbol) (bits : BitString) : Outcome Symbol :=
  if label = [] then if active = 0 then .accepted target else .exhausted
  else match labelValue label with
    | none => .exhausted
    | some bit => bitOutcome bit capacity active formula n bits

theorem selectLabel_empty (capacity active : ℕ) (formula : Formula) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (count : m.store 10 = List.replicate active .one)
    (random : m.randomHead = 0) (output : m.output = []) (label : m.store 3 = []) :
    ∃ ticks ≤ labelBudget n bits m, ∃ result,
      selectLabel.Runs n bits m ticks result ∧
        result.outcome = labelOutcome capacity active formula n (m.store 34) [] bits := by
  cases active with
  | zero =>
      obtain ⟨final,emits,emitted⟩ := emitSaved_runs bits m index
      have inner : (Command.branch 10 fun active => if active.1.isSome then .drain else emitSaved).Runs
          n bits m (1+4*(m.store 34).length) (.done final) := by
        apply Command.Runs.branch
        simpa [observe,count] using emits
      refine ⟨1+(1+4*(m.store 34).length),?_,.done final,?_,?_⟩
      · dsimp only [labelBudget]; omega
      · apply Command.Runs.branch
        simpa [selectLabel,observe,label] using inner
      · simpa [Result.outcome,labelOutcome,output] using emitted
  | succ active =>
      have drain : Command.drain.Runs n bits m bits.length .exhausted := by
        simpa only [random,Nat.sub_zero] using Command.Runs.drain (n := n) (bits := bits) m
      have inner : (Command.branch 10 fun active => if active.1.isSome then .drain else emitSaved).Runs
          n bits m (1+bits.length) .exhausted := by
        apply Command.Runs.branch
        simpa [observe,count,List.replicate_succ] using drain
      refine ⟨1+(1+bits.length),?_,.exhausted,?_,?_⟩
      · dsimp only [labelBudget]; omega
      · apply Command.Runs.branch
        simpa [selectLabel,observe,label] using inner
      · simp [Result.outcome,labelOutcome]

theorem selectLabel_bit (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (counter : m.store 32 = List.replicate n .zero)
    (represented : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ m.store)
    (clock : NativeBody.tokenCount formula ≤ (m.store 16).length)
    (random : m.randomHead = 0) (output : m.output = []) (label : m.store 3 = [bitSymbol bit]) :
    ∃ ticks ≤ labelBudget n bits m, ∃ result,
      selectLabel.Runs n bits m ticks result ∧
        result.outcome = labelOutcome capacity active formula n (m.store 34) [bitSymbol bit] bits := by
  obtain ⟨ticks,cost,result,run,outcome⟩ := chooseBit_singleton bit bound formula valid n bits m index counter represented clock random output label
  refine ⟨1+ticks,?_,result,?_,?_⟩
  · cases bit <;> dsimp only [labelBudget] at * <;> omega
  · apply Command.Runs.branch
    cases bit <;> simpa [selectLabel,observe,label,bitSymbol] using run
  · simpa [labelOutcome] using outcome

theorem selectLabel_invalid (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (random : m.randomHead = 0)
    (label : List Symbol) (contents : m.store 3 = label) (nonempty : label ≠ [])
    (invalid : labelValue label = none) :
    ∃ ticks ≤ labelBudget n bits m, selectLabel.Runs n bits m ticks .exhausted := by
  have drain : Command.drain.Runs n bits m bits.length .exhausted := by
    simpa only [random,Nat.sub_zero] using Command.Runs.drain (n := n) (bits := bits) m
  cases label with
  | nil => exact False.elim (nonempty rfl)
  | cons symbol rest =>
      cases symbol
      case zero =>
        cases rest with
        | nil => simp [labelValue] at invalid
        | cons second rest =>
            have run := chooseBit_bad_tail false n bits m index random .zero second rest contents
            refine ⟨1+(3+bits.length),?_,?_⟩
            · dsimp only [labelBudget]; omega
            · apply Command.Runs.branch
              simpa [selectLabel,observe,contents] using run
      case one =>
        cases rest with
        | nil => simp [labelValue] at invalid
        | cons second rest =>
            have run := chooseBit_bad_tail true n bits m index random .one second rest contents
            refine ⟨1+(3+bits.length),?_,?_⟩
            · dsimp only [labelBudget]; omega
            · apply Command.Runs.branch
              simpa [selectLabel,observe,contents] using run
      all_goals
        refine ⟨1+bits.length,?_,?_⟩
        · dsimp only [labelBudget]; omega
        · apply Command.Runs.branch
          simpa [selectLabel,observe,contents] using drain

theorem selectLabel_runs {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (counter : m.store 32 = List.replicate n .zero)
    (represented : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ m.store)
    (clock : NativeBody.tokenCount formula ≤ (m.store 16).length)
    (random : m.randomHead = 0) (output : m.output = []) (label : List Symbol) (contents : m.store 3 = label) :
    ∃ ticks ≤ labelBudget n bits m, ∃ result,
      selectLabel.Runs n bits m ticks result ∧
        result.outcome = labelOutcome capacity active formula n (m.store 34) label bits := by
  by_cases empty : label = []
  · have actual : m.store 3 = [] := contents.trans empty
    have run := selectLabel_empty capacity active formula n bits m index represented.2.2.1 random output actual
    simpa only [empty] using run
  · cases decoded : labelValue label with
    | none =>
        obtain ⟨ticks,cost,run⟩ := selectLabel_invalid n bits m index random label contents empty decoded
        exact ⟨ticks,cost,.exhausted,run,by simp [Result.outcome,labelOutcome,empty,decoded]⟩
    | some bit =>
        have labelEq := InverseNative.labelValue_some label bit decoded
        have actual : m.store 3 = [bitSymbol bit] := contents.trans labelEq
        have run := selectLabel_bit bit bound formula valid n bits m index counter represented clock random output actual
        simpa only [labelEq] using run

def valueOutcome : Option (List Symbol) → Outcome Symbol
  | none => .exhausted
  | some word => .accepted word

theorem labelOutcome_eq_value {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ)
    (length : (formula.encode capacity active).length = n) (label : List Symbol) (bits : BitString) :
    labelOutcome capacity active formula n (formula.encode capacity active) label bits =
      valueOutcome (value n (formula.encode capacity active) label bits) := by
  by_cases empty : label = []
  · subst label
    rw [value_empty bound formula valid]
    by_cases zero : active = 0
    · subst active; simp [labelOutcome,valueOutcome,length]
    · simp [labelOutcome,valueOutcome,zero]
  · cases decoded : labelValue label with
    | none => simp [value_invalid n _ label bits empty decoded,labelOutcome,empty,decoded,valueOutcome]
    | some bit =>
        have labelEq := InverseNative.labelValue_some label bit decoded
        subst label
        rw [value_bit bound formula valid]
        by_cases more : active+1 ≤ capacity <;> by_cases enough : n ≤ bits.length <;>
          simp [labelOutcome,bitOutcome,valueOutcome,length,more,enough]

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
