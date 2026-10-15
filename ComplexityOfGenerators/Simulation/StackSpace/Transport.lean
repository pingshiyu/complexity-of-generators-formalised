import ComplexityOfGenerators.Simulation.StackSpace.Trace

/-! Change a routine's stack alphabet and finite local-state representation.
Both encodings have left inverses. The simulation preserves every stack length,
so extending the interpreter alphabet with input symbols costs no extra cells. -/

namespace ComplexityOfGenerators.Simulation.StackSpace

open Turing
set_option backward.isDefEq.respectTransparency false

variable {S T Q V W : Type} {k : ℕ}

def transportCode (write : S → T) (read : T → S) (pack : V → W) (unpack : W → V) :
    Stmt S Q V k → Stmt T Q W k
  | .push j f rest => .push j (fun v => write (f (unpack v))) (transportCode write read pack unpack rest)
  | .pop j f rest => .pop j (fun v s => pack (f (unpack v) (s.map read))) (transportCode write read pack unpack rest)
  | .peek j f rest => .peek j (fun v s => pack (f (unpack v) (s.map read))) (transportCode write read pack unpack rest)
  | .load f rest => .load (fun v => pack (f (unpack v))) (transportCode write read pack unpack rest)
  | .branch f yes no => .branch (fun v => f (unpack v))
      (transportCode write read pack unpack yes) (transportCode write read pack unpack no)
  | .goto f => .goto (fun v => f (unpack v))
  | .halt => .halt

def transportConfig (write : S → T) (pack : V → W) (c : Source S Q V k) : Source T Q W k :=
  ⟨c.l, pack c.var, fun j => (c.stk j).map write⟩

variable (write : S → T) (read : T → S) (pack : V → W) (unpack : W → V)
variable (symbols : Function.LeftInverse read write) (locals : Function.LeftInverse unpack pack)

private theorem map_update (stk : Fin (k + 1) → List S) (j : Fin (k + 1)) (word : List S) :
    (fun i => (Function.update stk j word i).map write) =
      Function.update (fun i => (stk i).map write) j (word.map write) := by
  funext i
  by_cases h : i = j <;> simp [h]

include symbols in
private theorem read_head (word : List S) : ((word.map write).head?).map read = word.head? := by
  cases word with
  | nil => rfl
  | cons a rest => simp [symbols a]

include symbols locals

theorem transport_stepAux (code : Stmt S Q V k) (v : V) (stk : Fin (k + 1) → List S) :
    TM2.stepAux (transportCode write read pack unpack code) (pack v) (fun j => (stk j).map write) =
      transportConfig write pack (TM2.stepAux code v stk) := by
  induction code generalizing v stk with
  | push j f rest ih =>
      simpa only [transportCode, TM2.stepAux, locals v, ← List.map_cons, ← map_update]
        using ih v (Function.update stk j (f v :: stk j))
  | pop j f rest ih =>
      simpa only [transportCode, TM2.stepAux, locals v, read_head write read symbols,
        ← List.map_tail, ← map_update] using ih (f v (stk j).head?) (Function.update stk j (stk j).tail)
  | peek j f rest ih =>
      simpa only [transportCode, TM2.stepAux, locals v, read_head write read symbols]
        using ih (f v (stk j).head?) stk
  | load f rest ih => simpa only [transportCode, TM2.stepAux, locals v] using ih (f v) stk
  | branch f yes no ihYes ihNo =>
      cases h : f v <;> simp only [transportCode, TM2.stepAux, locals v, h, Bool.cond_false, Bool.cond_true]
      · exact ihNo v stk
      · exact ihYes v stk
  | goto f => simp [transportCode, TM2.stepAux, transportConfig, locals v]
  | halt => rfl

theorem transport_step (P : Q → Stmt S Q V k) (c : Source S Q V k) :
    TM2.step (fun q => transportCode write read pack unpack (P q)) (transportConfig write pack c) =
      (TM2.step P c).map (transportConfig write pack) := by
  rcases c with ⟨label, v, stk⟩
  cases label <;> simp [TM2.step, transportConfig, transport_stepAux write read pack unpack symbols locals]

omit symbols locals read unpack in
theorem transport_bound (c : Source S Q V k) (r : ℕ) (bound : Within r c) :
    Within r (transportConfig write pack c) := by
  intro j
  simpa [transportConfig] using bound j

/-- Transport a complete operational trace without increasing its space
bound. The finite-state encodings cannot inspect stack contents. -/
theorem Trace.transport {P : Q → Stmt S Q V k} {r : ℕ} {a b : Source S Q V k}
    (path : Trace P r a b) :
    Trace (fun q => transportCode write read pack unpack (P q)) r
      (transportConfig write pack a) (transportConfig write pack b) := by
  induction path with
  | refl c bound => exact .refl _ (transport_bound write pack c r bound)
  | step bound next tail ih =>
      exact .step (transport_bound write pack _ r bound)
        (by rw [transport_step write read pack unpack symbols locals, next]; rfl) ih

end ComplexityOfGenerators.Simulation.StackSpace
