import ComplexityOfGenerators.Foundations.ExecutionRegions

/-! A native path whose random cursor does not advance reads no random bits.
It can therefore be replayed on any random tape at any cursor, with exactly the
same native instructions and elapsed time. -/
namespace ComplexityOfGenerators.Machine
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O)

def rebaseRandom (c : Configuration M) (cursor : ℕ) : Configuration M := {c with randomHead:=cursor}

@[simp] theorem rebaseRandom_twice (c : Configuration M) (first second : ℕ) :
    M.rebaseRandom (M.rebaseRandom c first) second=M.rebaseRandom c second := by cases c; rfl

@[simp] theorem rebaseRandom_self (c : Configuration M) : M.rebaseRandom c c.randomHead=c := by cases c; rfl

theorem rebaseRandom_eq (c : Configuration M) (cursor : ℕ) (same : cursor=c.randomHead) :
    M.rebaseRandom c cursor=c := by rw [same,rebaseRandom_self]

theorem next_randomHead_mono (data : InputData I A) (bits : BitString)
    (c d : Configuration M) (edge : M.next data bits c=.running d) : c.randomHead≤d.randomHead := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [next,action] at edge
  | reject => simp [next,action] at edge
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [next,action,lookup] at edge
      | some bit =>
          simp only [next,action,lookup,RunState.running.injEq] at edge
          subst d
          exact Nat.le_succ _
  | step state write work input auxiliary index emit =>
      rw [M.next_step data bits c state write work input auxiliary index emit action] at edge
      cases edge
      exact le_rfl

theorem Steps.randomHead_mono {data : InputData I A} {bits : BitString} {c d : Configuration M} {ticks : ℕ}
    (path : M.Steps data bits c ticks d) : c.randomHead≤d.randomHead := by
  induction path with
  | refl => exact le_rfl
  | tail path edge ih => exact ih.trans (next_randomHead_mono M _ _ _ _ edge)

theorem next_rebase_random (data : InputData I A) (bits otherBits : BitString)
    (c d : Configuration M) (edge : M.next data bits c=.running d)
    (stable : d.randomHead=c.randomHead) (cursor : ℕ) :
    M.next data otherBits (M.rebaseRandom c cursor)=.running (M.rebaseRandom d cursor) := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [next,action] at edge
  | reject => simp [next,action] at edge
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [next,action,lookup] at edge
      | some bit =>
          simp only [next,action,lookup,RunState.running.injEq] at edge
          subst d
          change c.randomHead+1=c.randomHead at stable
          omega
  | step state write work input auxiliary index emit =>
      rw [M.next_step data bits c state write work input auxiliary index emit action] at edge
      cases edge
      have targetAction : M.transition (M.rebaseRandom c cursor).state
          data.input[(M.rebaseRandom c cursor).inputHead]?
          data.auxiliary[(M.rebaseRandom c cursor).auxiliaryHead]?
          (if (M.rebaseRandom c cursor).indexHead<data.index then some () else none)
          ((M.rebaseRandom c cursor).work (M.rebaseRandom c cursor).workHead)=
          .step state write work input auxiliary index emit := action
      rw [M.next_step data otherBits (M.rebaseRandom c cursor) state write work input auxiliary index emit targetAction]
      cases write <;> cases emit <;> rfl

theorem Steps.rebase_random {data : InputData I A} {bits : BitString} {c d : Configuration M} {ticks : ℕ}
    (path : M.Steps data bits c ticks d) (stable : d.randomHead=c.randomHead)
    (otherBits : BitString) (cursor : ℕ) :
    M.Steps data otherBits (M.rebaseRandom c cursor) ticks (M.rebaseRandom d cursor) := by
  induction path with
  | refl => exact .refl
  | @tail ticks current next path edge ih =>
      have before := path.randomHead_mono M
      have after := next_randomHead_mono M data bits current next edge
      have currentEqual : current.randomHead=c.randomHead := by omega
      have nextEqual : next.randomHead=current.randomHead := by omega
      exact (ih currentEqual).tail (next_rebase_random M data bits otherBits current next edge nextEqual cursor)

end ComplexityOfGenerators.Machine
