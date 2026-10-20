import ComplexityOfGenerators.Simulation.WordStack.Local

/-! Register renaming and finite-alphabet embeddings for local routines. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Local

variable {S T : Type} {k l : ℕ}

def rename (f : Fin k → Fin l) : Local S k → Local S l
  | .skip => .skip
  | .act j a => .act (f j) a
  | .read j next => .read (f j) (fun o => (next o).rename f)
  | .seq a b => (a.rename f).seq (b.rename f)

theorem rename_eval (f : Fin k ↪ Fin l) (c : Local S k) (s : Store S l) :
    (c.rename f).eval s ∘ f = c.eval (s ∘ f) := by
  induction c generalizing s with
  | skip => rfl
  | act j a => exact Function.update_comp_eq_of_injective s f.injective j _
  | read j next ih => exact ih _ s
  | seq a b ha hb =>
    change (b.rename f).eval ((a.rename f).eval s) ∘ f = b.eval (a.eval (s ∘ f))
    rw [hb, ha]

theorem rename_frame (f : Fin k → Fin l) (c : Local S k) (s : Store S l) (j : Fin l)
    (outside : ∀ i, j ≠ f i) : (c.rename f).eval s j = s j := by
  induction c generalizing s with
  | skip => rfl
  | act i a => exact Function.update_of_ne (outside i) ..
  | read i next ih => exact ih _ s
  | seq a b ha hb => exact (hb _).trans (ha _)

def mapAction (f : S → T) : Action S → Action T
  | .stay => .stay
  | .pop => .pop
  | .push a => .push (f a)

theorem mapAction_apply (f : S → T) (a : Action S) (w : List S) :
    (mapAction f a).apply (w.map f) = (a.apply w).map f := by
  cases a <;> simp [mapAction, Action.apply, List.map_tail]

def mapSymbols (f : S → T) (g : T → S) : Local S k → Local T k
  | .skip => .skip
  | .act j a => .act j (mapAction f a)
  | .read j next => .read j (fun o => (next (o.map g)).mapSymbols f g)
  | .seq a b => (a.mapSymbols f g).seq (b.mapSymbols f g)

def mapStore (f : S → T) (s : Store S k) : Store T k := fun j => (s j).map f

theorem mapStore_update (f : S → T) (s : Store S k) (j : Fin k) (w : List S) :
    mapStore f (Function.update s j w) = Function.update (mapStore f s) j (w.map f) := by
  funext i
  by_cases equal : i = j <;> simp [mapStore, equal]

theorem mapSymbols_eval (f : S → T) (g : T → S) (retract : Function.LeftInverse g f)
    (c : Local S k) (s : Store S k) :
    (c.mapSymbols f g).eval (mapStore f s) = mapStore f (c.eval s) := by
  induction c generalizing s with
  | skip => rfl
  | act j a => simp only [mapSymbols, eval, mapStore_update, mapStore, mapAction_apply]
  | read j next ih =>
    have head : ((mapStore f s j).head?).map g = (s j).head? := by
      cases h : s j with
      | nil => simp [mapStore, h]
      | cons a rest => simp [mapStore, h, retract a]
    simpa only [mapSymbols, eval_read, head] using ih (s j).head? s
  | seq a b ha hb => simp only [mapSymbols, eval_seq, ha, hb]

end ComplexityOfGenerators.Simulation.WordStack.Local
