import ComplexityOfGenerators.Foundations.SpaceBounds
import ComplexityOfGenerators.Proofs.PaperCertificateBounds

/-! Deterministically choose the false branch of a native decision machine.
The source auxiliary and index tapes are empty. The target can receive arbitrary
certificate input, which it ignores. Source runs on a sufficiently long all-
false random tape are simulated with exactly the same transition count. -/
namespace ComplexityOfGenerators.PaperCertificates.FalseChoice
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} [Fintype A] (M : Machine I Bool O)

def machine : Machine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := inferInstance
  outputFinite := M.outputFinite
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition q input _ _ work :=
    match M.transition q input none none work with
    | .accept => .accept
    | .reject => .reject
    | .readRandom no _ => .step no none .stay .stay .stay .stay none
    | .step next write work input _ _ emit => .step next write work input .stay .stay emit

def configuration (c : Configuration M) : Configuration (machine (A:=A) M) :=
  ⟨c.state,c.inputHead,0,0,0,c.workHead,c.work,c.visited,c.output⟩

def state : RunState M→RunState (machine (A:=A) M)
  | .running c => .running (configuration M c)
  | .halted result => .halted result

theorem deterministic : (machine (A:=A) M).Deterministic := by
  intro q input auxiliary index work
  dsimp only [machine]
  cases M.transition q input none none work <;> trivial

theorem observe (word : Word I) (certificate : Word A) (bits : BitString)
    (size : ℕ) (c : Configuration M) (available : c.randomHead<size) :
    (machine M).observe {input:=word,auxiliary:=certificate} bits (configuration M c)=
      state M (M.observe (decisionData word) (List.replicate size false) c) := by
  simp only [Machine.observe,machine,configuration,decisionData,List.getElem?_nil,Nat.not_lt_zero,↓reduceIte]
  cases action : M.transition c.state word[c.inputHead]? none none (c.work c.workHead) <;>
    simp only [action,state] <;> first | rfl | (simp [available,configuration])

theorem next (word : Word I) (certificate : Word A) (bits : BitString)
    (size : ℕ) (c : Configuration M) (available : c.randomHead<size)
    (inputBound : c.inputHead≤word.length) (head : c.workHead∈c.visited) :
    (machine M).next {input:=word,auxiliary:=certificate} bits (configuration M c)=
      state M (M.next (decisionData word) (List.replicate size false) c) := by
  simp only [Machine.next,machine,configuration,decisionData,List.getElem?_nil,Nat.not_lt_zero,↓reduceIte]
  cases action : M.transition c.state word[c.inputHead]? none none (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | step next write work input auxiliary index emit =>
      cases write <;> cases emit <;>
        simp [action,state,configuration,Move.onInput]
  | readRandom no yes =>
      have lookup : (List.replicate size false)[c.randomHead]?=some false := by simp [available]
      simp [action,lookup,state,configuration,Move.onInt,Move.onInput,
        Nat.min_eq_left inputBound,Finset.insert_eq_of_mem head]

theorem run (word : Word I) (certificate : Word A) (bits : BitString)
    (size ticks : ℕ) (long : ticks<size) :
    (machine M).run {input:=word,auxiliary:=certificate} bits ticks=
      state M (M.run (decisionData word) (List.replicate size false) ticks) := by
  induction ticks with
  | zero =>
      simpa only [Machine.run,Machine.initialConfiguration,configuration,machine] using
        observe M word certificate bits size M.initialConfiguration (by simp [Machine.initialConfiguration];omega)
  | succ ticks ih =>
      rw [Machine.run,Machine.run,ih (by omega)]
      cases previous : M.run (decisionData word) (List.replicate size false) ticks with
      | halted result => rfl
      | running c =>
          have bound := M.run_configurationBound _ _ ticks c previous
          have geometry := M.run_geometry _ _ ticks c previous
          simp only [state]
          rw [next M word certificate bits size c (by have h:=bound.randomHead;omega) bound.inputHead geometry.head]
          cases step : M.next (decisionData word) (List.replicate size false) c with
          | halted result => rfl
          | running d =>
              have after := M.next_executionBound _ (List.replicate size false) ticks c bound
              rw [step] at after
              exact observe M word certificate bits size d (by have h:=after.randomHead;omega)

theorem timeBound (word : Word I) (certificate : Word A) (ticks : ℕ)
    (bound : M.TimeBound (decisionData word) ticks) :
    (machine M).TimeBound {input:=word,auxiliary:=certificate} ticks := by
  intro bits
  obtain ⟨result,source⟩ := bound (List.replicate (ticks+1) false)
  exact ⟨result,by rw [run M word certificate bits (ticks+1) ticks (by omega),source];rfl⟩

theorem accepts_iff (word : Word I) (certificate : Word A) (bits : BitString)
    (size ticks : ℕ) (long : ticks<size)
    (bound : M.TimeBound (decisionData word) ticks) :
    (machine M).Accepts {input:=word,auxiliary:=certificate} bits↔
      M.Accepts (decisionData word) (List.replicate size false) := by
  have targetBound := timeBound M word certificate ticks bound
  constructor
  · rintro ⟨output,produced⟩
    have accepted := (machine M).produces_at_bound _ bits ticks output (targetBound bits) produced
    rw [run M word certificate bits size ticks long] at accepted
    cases source : M.run (decisionData word) (List.replicate size false) ticks with
    | running c => simp [source,state] at accepted
    | halted result =>
        have same : result=.accepted output := by simpa [source,state] using accepted
        exact ⟨output,ticks,by simpa [same] using source⟩
  · rintro ⟨output,produced⟩
    have accepted := M.produces_at_bound _ _ ticks output (bound _) produced
    exact ⟨output,ticks,by rw [run M word certificate bits size ticks long,accepted];rfl⟩

end ComplexityOfGenerators.PaperCertificates.FalseChoice
