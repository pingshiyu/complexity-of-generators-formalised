import ComplexityOfGenerators.Simulation.WordStack.SourceCorrectness
import ComplexityOfGenerators.Simulation.WordStack.LocalEmbedding
import ComplexityOfGenerators.Simulation.WordStack.LocalLoop

/-! Clocked source calls embedded into a larger register bank and alphabet. -/

namespace ComplexityOfGenerators.Simulation.WordStack

namespace Local

variable {S O : Type} {k : ℕ}

@[simp] theorem iterate_index (c : Local S k) (t : ℕ) (m : Memory S O k) :
    (c.apply^[t] m).indexHead = m.indexHead := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [Function.iterate_succ_apply', apply_index] using ih

@[simp] theorem iterate_random (c : Local S k) (t : ℕ) (m : Memory S O k) :
    (c.apply^[t] m).randomHead = m.randomHead := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [Function.iterate_succ_apply', apply_random] using ih

@[simp] theorem iterate_output (c : Local S k) (t : ℕ) (m : Memory S O k) :
    (c.apply^[t] m).output = m.output := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [Function.iterate_succ_apply', apply_output] using ih

theorem iterate_frame (c : Local S k) (j : Fin k) (frame : ∀ s, c.eval s j = s j)
    (t : ℕ) (m : Memory S O k) : (c.apply^[t] m).store j = m.store j := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [Function.iterate_succ_apply', apply_store, frame] using ih

end Local

namespace Source

variable {I A O S Output : Type} {k : ℕ} (M : Machine I A O)

def body (encode : Symbol M → S) (decode : S → Symbol M) (slots : Fin 11 ↪ Fin k) : Local S k :=
  ((step M).mapSymbols encode decode).rename slots

theorem body_eval (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (slots : Fin 11 ↪ Fin k)
    (s : Snapshot M) (store : Local.Store S k)
    (rep : store ∘ slots = Local.mapStore encode (s.store M)) :
    (body M encode decode slots).eval store ∘ slots = Local.mapStore encode ((s.step M).store M) := by
  rw [body, Local.rename_eval, rep, Local.mapSymbols_eval encode decode retract, step_eval]

theorem counted_eval (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (slots : Fin 11 ↪ Fin k)
    (clock : Fin k) (outside : ∀ i, slots i ≠ clock)
    (s : Snapshot M) (store : Local.Store S k)
    (rep : store ∘ slots = Local.mapStore encode (s.store M)) :
    (Local.counted clock (body M encode decode slots)).eval store ∘ slots =
      Local.mapStore encode ((s.step M).store M) := by
  apply body_eval M encode decode retract slots s
  rw [Local.eval_pop, Function.update_comp_eq_of_forall_ne _ _ outside, rep]

theorem counted_iterate (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (slots : Fin 11 ↪ Fin k)
    (clock : Fin k) (outside : ∀ i, slots i ≠ clock)
    (s : Snapshot M) (m : Memory S Output k)
    (rep : m.store ∘ slots = Local.mapStore encode (s.store M)) (t : ℕ) :
    ((Local.counted clock (body M encode decode slots)).apply^[t] m).store ∘ slots =
      Local.mapStore encode (((Snapshot.step M)^[t] s).store M) := by
  induction t with
  | zero => exact rep
  | succ t ih =>
    simpa only [Function.iterate_succ_apply', Local.apply_store] using
      counted_eval M encode decode retract slots clock outside _ _ ih

/-- The source call has constant overhead per source step and leaves all
registers outside its assigned bank and clock unchanged. -/
theorem clocked_runs [Fintype S] (encode : Symbol M → S) (decode : S → Symbol M)
    (retract : Function.LeftInverse decode encode) (slots : Fin 11 ↪ Fin k)
    (clock : Fin k) (outside : ∀ i, slots i ≠ clock)
    (s : Snapshot M) {n : ℕ} (bits : BitString) (m : Memory S Output k)
    (bounded : m.indexHead ≤ n) (rep : m.store ∘ slots = Local.mapStore encode (s.store M)) :
    ∃ t ≤ (m.store clock).length * ((body M encode decode slots).bound + 4), ∃ finish,
      (Local.clocked clock (body M encode decode slots)).Runs n bits m t (.done finish) ∧
      finish.store ∘ slots = Local.mapStore encode
        (((Snapshot.step M)^[(m.store clock).length] s).store M) ∧
      finish.store clock = [] ∧ finish.indexHead = m.indexHead ∧
      finish.randomHead = m.randomHead ∧ finish.output = m.output ∧
      ∀ j, j ≠ clock → (∀ i, j ≠ slots i) → finish.store j = m.store j := by
  obtain ⟨t, cost, run, cleared⟩ := Local.repeat_runs clock (body M encode decode slots)
    (fun store => Local.rename_frame slots _ store clock (fun i => (outside i).symm)) bits m bounded
  refine ⟨t, cost, _, run, counted_iterate M encode decode retract slots clock outside s m rep _,
    cleared, Local.iterate_index .., Local.iterate_random .., Local.iterate_output .., ?_⟩
  intro j notClock notSlot
  apply Local.iterate_frame
  intro store
  change (body M encode decode slots).eval ((Local.pop clock).eval store) j = store j
  rw [body, Local.rename_frame _ _ _ _ notSlot, Local.eval_pop, Function.update_of_ne notClock]

end Source
end ComplexityOfGenerators.Simulation.WordStack
