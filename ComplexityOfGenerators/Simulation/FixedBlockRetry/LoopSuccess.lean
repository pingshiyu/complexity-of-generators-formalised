import ComplexityOfGenerators.Simulation.FixedBlockRetry.Loop

/-! Exact successful retry prefixes, including the random-head position.
Unlike a whole-tape bound, this cost depends only on attempted blocks and is
therefore suitable for several fresh calls in one compiled controller. -/
namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S O Payload : Type} [Fintype S] (unitSymbol : S) (bitSymbol : Bool → S)
    (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (decode : S → Option Payload) (f : ℕ → BitString → Option (List Payload))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase)
    (frame : ∀ s, (phase.eval s 22).length = (s 22).length)

include correct bounded frame in
theorem loop_runs_success_at_index_with_post (Q : Local.Store S 35 → Prop)
    (post : ∀ (n : ℕ) (block : BitString) (s : Local.Store S 35), block.length = width n →
      (s 13).length = n → (s 22).length = n → s 17 = block.map bitSymbol → Q (phase.eval s))
    (restored : ∀ s, Q s → Q ((restoreIndex (O := O) unitSymbol).eval s))
    (n attempts inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (within : n ≤ inputIndex) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : m.randomHead + (attempts+1)*width n ≤ bits.length)
    (failed : ∀ j < attempts, f n ((bits.drop (m.randomHead + j*width n)).take (width n)) = none)
    (word : List Payload)
    (success : f n ((bits.drop (m.randomHead + attempts*width n)).take (width n)) = some word) :
    ∃ t ≤ (attempts+1)*(attemptBudget width cap time n+2), ∃ next,
      (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits m t (.done next) ∧
      State n (cap n) next ∧ next.indexHead = m.indexHead ∧ next.randomHead = m.randomHead+(attempts+1)*width n ∧ Q next.store ∧
      next.store 32 = [unitSymbol] ∧ (next.store 31).filterMap decode = word := by
  induction attempts generalizing m with
  | zero =>
    have full : width n ≤ bits.length - m.randomHead := by simp only [Nat.zero_add, Nat.one_mul] at enough; omega
    obtain ⟨ticks, cost, next, run, nextState, nextOrigin, nextHead, nextPost, flag, payload⟩ :=
      attempt_full_at_index_with_post unitSymbol bitSymbol width cap time phase decode f correct bounded frame Q post restored
        n inputIndex bits m state within indexBudget widthBudget full
    have output : f n ((bits.drop m.randomHead).take (width n)) = some word := by simpa using success
    have flagValue : next.store 32 = [unitSymbol] := by simpa [output, flagWord] using flag
    have stop : (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits next 0 (.done next) :=
      Command.Runs.loop_stop next 32 _ _ (by simp [observe, flagValue])
    refine ⟨1+ticks+1+0, by simpa using (by omega : 1+ticks+1 ≤ attemptBudget width cap time n+2), next,
      Command.Runs.loop m next 32 _ _ ticks 0 _ (by simp [observe, waiting]) run stop,
      nextState, nextOrigin, ?_, nextPost, flagValue, payload word output⟩
    simpa using nextHead
  | succ attempts ih =>
    have full : width n ≤ bits.length - m.randomHead := by
      have one : m.randomHead+width n ≤ bits.length := by nlinarith
      omega
    obtain ⟨ticks, cost, middle, run, middleState, middleOrigin, middleHead, middlePost, flag, payload⟩ :=
      attempt_full_at_index_with_post unitSymbol bitSymbol width cap time phase decode f correct bounded frame Q post restored
        n inputIndex bits m state within indexBudget widthBudget full
    have first : f n ((bits.drop m.randomHead).take (width n)) = none := by
      simpa using failed 0 (by omega)
    have middleWaiting : middle.store 32 = [] := by simpa [first, flagWord] using flag
    have offset (j : ℕ) : middle.randomHead + j*width n = m.randomHead+(j+1)*width n := by
      rw [middleHead]
      ring
    have laterEnough : middle.randomHead+(attempts+1)*width n ≤ bits.length := by
      rw [offset]
      exact enough
    have laterFailed (j : ℕ) (earlier : j < attempts) :
        f n ((bits.drop (middle.randomHead+j*width n)).take (width n)) = none := by
      rw [offset]
      exact failed (j+1) (by omega)
    have laterSuccess : f n ((bits.drop (middle.randomHead+attempts*width n)).take (width n)) = some word := by
      rw [offset]
      exact success
    obtain ⟨restTicks, restCost, next, restRun, nextState, nextOrigin, nextHead, nextPost, nextFlag, nextWord⟩ :=
      ih middle middleState middleWaiting laterEnough laterFailed laterSuccess
    refine ⟨1+ticks+1+restTicks, ?_, next,
      Command.Runs.loop m middle 32 _ _ ticks restTicks _ (by simp [observe, waiting]) run restRun,
      nextState, nextOrigin.trans middleOrigin, ?_, nextPost, nextFlag, nextWord⟩
    · nlinarith
    · rw [nextHead, offset]

include correct bounded frame in
theorem loop_runs_success_at_index_preserves_head (n attempts inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (within : n ≤ inputIndex) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : m.randomHead + (attempts+1)*width n ≤ bits.length)
    (failed : ∀ j < attempts, f n ((bits.drop (m.randomHead + j*width n)).take (width n)) = none)
    (word : List Payload)
    (success : f n ((bits.drop (m.randomHead + attempts*width n)).take (width n)) = some word) :
    ∃ t ≤ (attempts+1)*(attemptBudget width cap time n+2), ∃ next,
      (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits m t (.done next) ∧
      State n (cap n) next ∧ next.indexHead = m.indexHead ∧ next.randomHead = m.randomHead+(attempts+1)*width n ∧
      next.store 32 = [unitSymbol] ∧ (next.store 31).filterMap decode = word := by
  obtain ⟨ticks, cost, next, run, state, origin, head, _, flag, payload⟩ :=
    loop_runs_success_at_index_with_post unitSymbol bitSymbol width cap time phase decode f correct bounded frame
      (fun _ => True) (by intros; trivial) (by intros; trivial) n attempts inputIndex bits m state waiting within indexBudget widthBudget
      enough failed word success
  exact ⟨ticks, cost, next, run, state, origin, head, flag, payload⟩

include correct bounded frame in
theorem loop_runs_success_at_index (n attempts inputIndex : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (within : n ≤ inputIndex) (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : m.randomHead + (attempts+1)*width n ≤ bits.length)
    (failed : ∀ j < attempts, f n ((bits.drop (m.randomHead + j*width n)).take (width n)) = none)
    (word : List Payload)
    (success : f n ((bits.drop (m.randomHead + attempts*width n)).take (width n)) = some word) :
    ∃ t ≤ (attempts+1)*(attemptBudget width cap time n+2), ∃ next,
      (retryLoop unitSymbol bitSymbol width phase).Runs inputIndex bits m t (.done next) ∧
      State n (cap n) next ∧ next.randomHead = m.randomHead+(attempts+1)*width n ∧
      next.store 32 = [unitSymbol] ∧ (next.store 31).filterMap decode = word := by
  obtain ⟨ticks, cost, next, run, state, origin, head, flag, payload⟩ :=
    loop_runs_success_at_index_preserves_head unitSymbol bitSymbol width cap time phase decode f
      correct bounded frame n attempts inputIndex bits m state waiting within indexBudget widthBudget
      enough failed word success
  exact ⟨ticks, cost, next, run, state, head, flag, payload⟩

include correct bounded frame in
theorem loop_runs_success (n attempts : ℕ) (bits : BitString) (m : Memory S O 35)
    (state : State n (cap n) m) (waiting : m.store 32 = [])
    (indexBudget : n+1 ≤ cap n) (widthBudget : width n ≤ cap n)
    (enough : m.randomHead + (attempts+1)*width n ≤ bits.length)
    (failed : ∀ j < attempts, f n ((bits.drop (m.randomHead + j*width n)).take (width n)) = none)
    (word : List Payload)
    (success : f n ((bits.drop (m.randomHead + attempts*width n)).take (width n)) = some word) :
    ∃ t ≤ (attempts+1)*(attemptBudget width cap time n+2), ∃ next,
      (retryLoop unitSymbol bitSymbol width phase).Runs n bits m t (.done next) ∧
      State n (cap n) next ∧ next.randomHead = m.randomHead+(attempts+1)*width n ∧
      next.store 32 = [unitSymbol] ∧ (next.store 31).filterMap decode = word :=
  loop_runs_success_at_index unitSymbol bitSymbol width cap time phase decode f correct bounded frame
    n attempts n bits m state waiting le_rfl indexBudget widthBudget enough failed word success

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
