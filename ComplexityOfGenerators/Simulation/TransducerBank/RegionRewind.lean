import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- Rewinding a nonnegative work head preserves the existing space bound.
All other heads, tapes, choice position and output remain unchanged. -/
theorem rewind_regionSteps (data : InputData I A) (bits : BitString) (state finish : Q) (j : Fin k)
    (selected : B.select state=j)
    (table : ∀ input auxiliary index origin cell,
      B.transition state input auxiliary index origin cell=
        .step (if origin then finish else state) cell (if origin then .stay else .left) .stay .stay .stay none)
    (position radius : ℕ) (c : BankConfiguration O Q S k) (atState : c.state=state) (atHead : c.head j=position)
    (bounded : B.Bounded data radius c) :
    B.RegionSteps data bits radius c (position+1) {c with state:=finish,head:=Function.update c.head j 0} := by
  induction position generalizing c with
  | zero =>
      have heads : Function.update c.head j 0=c.head := by
        change c.head j=0 at atHead
        rw [←atHead]
        exact Function.update_eq_self _ _
      rw [heads]
      apply RegionSteps.step c finish (c.tape (B.select c.state) (c.head (B.select c.state))) .stay .stay .stay .stay none 0 _ bounded
      · simp [instruction,atState,selected,atHead,table]
      · rw [advance_stay B data c finish bounded.input bounded.auxiliary bounded.index]
        exact .refl _ (bounded.with_state B finish)
  | succ position ih =>
      let d : BankConfiguration O Q S k := {c with head:=Function.update c.head j (position:ℤ)}
      have nextBound : B.Bounded data radius d := by
        refine ⟨bounded.input,bounded.auxiliary,bounded.index,?_⟩
        intro i
        by_cases same : i=j
        · subst i
          have bound := bounded.head j
          rw [atHead] at bound
          simpa [d] using Nat.le_trans (Nat.le_succ position) bound
        · simpa [d,Function.update_of_ne same] using bounded.head i
      have step : B.RegionSteps data bits radius c 1 d := by
        have action : B.instruction data c=.step state (c.tape j (c.head j)) .left .stay .stay .stay none := by
          simp [instruction,atState,selected,atHead,table]
          omega
        apply RegionSteps.step c state _ .left .stay .stay .stay none 0 d bounded action
        have symbol : c.tape j (c.head j)=c.tape (B.select c.state) (c.head (B.select c.state)) := by rw [atState,selected]
        rw [symbol,advance_read B data c state .left bounded.input bounded.auxiliary bounded.index]
        have advanced : {c with state:=state,head:=Function.update c.head (B.select c.state) (Move.left.onInt (c.head (B.select c.state)))}=d := by
          simp [d,atState,selected,atHead,Move.onInt]
        rw [advanced]
        exact .refl _ nextBound
      have rest := ih d atState (by simp [d]) nextBound
      simpa [d,Function.update_idem,Nat.add_comm] using step.trans B rest

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
