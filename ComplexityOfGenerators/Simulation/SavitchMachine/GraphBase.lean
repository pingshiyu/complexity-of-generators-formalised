import ComplexityOfGenerators.Simulation.SavitchMachine.AlphabetSearch
import ComplexityOfGenerators.Simulation.SavitchMachine.BooleanTest

/-! Attach cache-restoring graph tests to the Savitch interpreter. The base
controller reads the frame kind, runs the appropriate finite test, and removes
exactly the completed frame using the verified load-and-erase routine. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.GraphBase

open Turing StackSpace Frames Complexity BooleanTest
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type}

/-- The columns that a base query must preserve until the frame is popped. -/
def frameMemory (word : List α) (fs : List Sav.Frm) : Fin 13 → List (Alphabet α) :=
  ![(column fs 0).map Alphabet.write, (column fs 1).map Alphabet.write,
    (column fs 2).map Alphabet.write, (column fs 3).map Alphabet.write,
    (column fs 4).map Alphabet.write, (column fs 5).map Alphabet.write,
    [], [], [], [], [], [], Alphabet.input word]

theorem encoded_eq {Q : Type} (word : List α) (q : Q) (s : Sav.Sst) :
    Alphabet.encoded word q s = localConfig q (status s) (frameMemory word s.stk) := by
  unfold Alphabet.encoded extendConfig localConfig
  congr 1
  funext j; fin_cases j <;> rfl

structure Context (radius : List α → ℕ) where
  word : List α
  frame : Sav.Frm
  parents : List Sav.Frm
  bound : ∀ j, (column (frame :: parents) j).length ≤ radius word

def memory {radius : List α → ℕ} (x : Context radius) : Fin 13 → List (Alphabet α) :=
  frameMemory x.word (x.frame :: x.parents)

theorem memory_bound {radius : List α → ℕ} (room : ∀ word, word.length ≤ radius word)
    (x : Context radius) (j : Fin 13) : (memory x j).length ≤ radius x.word := by
  have columns := x.bound
  simp only [column_cons, List.length_append, List.length_map, List.length_cons] at columns
  fin_cases j <;> simp [memory, frameMemory, Alphabet.input] <;>
    first | exact columns _ | exact room x.word


inductive Control (A R : Type)
  | start | accept (pc : A) | reach (pc : R)
  deriving Fintype

def kind (v : Status × Option (Alphabet α)) : Bool :=
  match v.2 with | some (.inr (some bit)) => bit | _ => false

def code (A R : Program (Alphabet α) 12) :
    Control A.Label R.Label → AlphabetSearch.Code α (Control A.Label R.Label)
  | .start => .peek 0 (fun v s => (v.1, s))
      (.branch kind
        (.load (fun v => (carrying v.1.answer false, none)) (.goto fun _ => .base (.accept A.entry)))
        (.load (fun v => (carrying v.1.answer false, none)) (.goto fun _ => .base (.reach R.entry))))
  | .accept pc => if pc = A.exit then .goto fun _ => loadPhase 0
      else embedCode (Function.Embedding.refl _) (fun q => .base (.accept q)) (A.code pc)
  | .reach pc => if pc = R.exit then .goto fun _ => loadPhase 0
      else embedCode (Function.Embedding.refl _) (fun q => .base (.reach q)) (R.code pc)

theorem correct (radius : List α → ℕ) (room : ∀ word, word.length ≤ radius word)
    (br : List α → List Bool → List Bool → Bool) (ba : List α → List Bool → Bool)
    (A R : Program (Alphabet α) 12)
    (accepts : Correct A (fun x : Context radius => radius x.word) memory (fun x => ba x.word x.frame.u))
    (reaches : Correct R (fun x : Context radius => radius x.word) memory (fun x => br x.word x.frame.u x.frame.v)) :
    ∀ word, AlphabetSearch.BaseCorrect .start (code A R) word (br word) (ba word) (radius word) := by
  intro word answer f fs _ bound
  let x : Context radius := ⟨word, f, fs, bound⟩
  let P := AlphabetSearch.program .start (code A R)
  have pop (result : Bool) : Trace P (radius word)
      (localConfig (loadPhase 0) (carrying answer result) (memory x))
      (AlphabetSearch.encoded word .dispatch ⟨false, answer, some result, fs⟩) := by
    have popped := pop_frame (SavitchMachine.program (.start : Control A.Label R.Label) (fun _ => .halt))
      erasePhase loadPhase (program_load _ _) (program_erase _ _) rfl
      (carrying answer result) f fs (radius word) bound
    have mapped := AlphabetSearch.lift_trace .start (code A R) popped
      (by simp [localConfig]) word (room word)
    change Trace P (radius word)
      (Alphabet.encoded word (loadPhase 0) ⟨false, answer, some result, f :: fs⟩)
      (Alphabet.encoded word .dispatch ⟨false, answer, some result, fs⟩) at mapped
    rw [encoded_eq] at mapped
    exact mapped
  have initial := AlphabetSearch.encoded_bound word
    (.base (.start : Control A.Label R.Label)) ⟨false, answer, none, f :: fs⟩
    (radius word) (room word) bound
  cases hk : f.kind with
  | true =>
      have body := (accepts x answer).rename_active (by simp [localConfig])
        (fun q => Label.base (Control.accept q)) P (by
          intro q nonhalt
          have ne : q ≠ A.exit := by rintro rfl; exact nonhalt A.exit_halts
          simp only [P, AlphabetSearch.program, code, ne, ↓reduceIte])
      simp only [renameConfig, localConfig, Option.map_some] at body
      have start : TM2.step P (AlphabetSearch.encoded word (.base .start) ⟨false, answer, none, f :: fs⟩) =
          some (localConfig (.base (.accept A.entry)) (carrying answer false) (memory x)) := by
        rw [show AlphabetSearch.encoded word (.base .start) ⟨false, answer, none, f :: fs⟩ =
          localConfig (.base (.start : Control A.Label R.Label)) (status ⟨false, answer, none, f :: fs⟩)
            (frameMemory word (f :: fs)) from encoded_eq _ _ _]
        simp [P, AlphabetSearch.program, code, TM2.step, TM2.stepAux, localConfig,
          kind, Alphabet.write, frameMemory, column_cons, field, hk, status, carrying, memory, x]
      have finish : TM2.step P (localConfig (.base (.accept A.exit))
          (carrying answer (ba word f.u)) (memory x)) =
          some (localConfig (loadPhase 0) (carrying answer (ba word f.u)) (memory x)) := by
        simp [P, AlphabetSearch.program, code, TM2.step, TM2.stepAux, localConfig]
      simpa only [Sav.baseVal, hk, ↓reduceIte] using
        Trace.step initial start (body.trans (.step body.end_bound finish (pop (ba word f.u))))
  | false =>
      have body := (reaches x answer).rename_active (by simp [localConfig])
        (fun q => Label.base (Control.reach q)) P (by
          intro q nonhalt
          have ne : q ≠ R.exit := by rintro rfl; exact nonhalt R.exit_halts
          simp only [P, AlphabetSearch.program, code, ne, ↓reduceIte])
      simp only [renameConfig, localConfig, Option.map_some] at body
      have start : TM2.step P (AlphabetSearch.encoded word (.base .start) ⟨false, answer, none, f :: fs⟩) =
          some (localConfig (.base (.reach R.entry)) (carrying answer false) (memory x)) := by
        rw [show AlphabetSearch.encoded word (.base .start) ⟨false, answer, none, f :: fs⟩ =
          localConfig (.base (.start : Control A.Label R.Label)) (status ⟨false, answer, none, f :: fs⟩)
            (frameMemory word (f :: fs)) from encoded_eq _ _ _]
        simp [P, AlphabetSearch.program, code, TM2.step, TM2.stepAux, localConfig,
          kind, Alphabet.write, frameMemory, column_cons, field, hk, status, carrying, memory, x]
      have finish : TM2.step P (localConfig (.base (.reach R.exit))
          (carrying answer (br word f.u f.v)) (memory x)) =
          some (localConfig (loadPhase 0) (carrying answer (br word f.u f.v)) (memory x)) := by
        simp [P, AlphabetSearch.program, code, TM2.step, TM2.stepAux, localConfig]
      simpa only [Sav.baseVal, hk, Bool.false_eq_true, ↓reduceIte] using
        Trace.step initial start (body.trans (.step body.end_bound finish (pop (br word f.u f.v))))

/-- Complete finite configuration-graph base control from proved, restorative
acceptance and reachability tests. -/
theorem exists_base (radius : List α → ℕ) (room : ∀ word, word.length ≤ radius word)
    (br : List α → List Bool → List Bool → Bool) (ba : List α → List Bool → Bool)
    (accepts : Realizable (fun x : Context radius => radius x.word) memory (fun x => ba x.word x.frame.u))
    (reaches : Realizable (fun x : Context radius => radius x.word) memory (fun x => br x.word x.frame.u x.frame.v)) :
    ∃ (B : Type) (_ : Fintype B) (entry : B) (base : B → AlphabetSearch.Code α B),
      ∀ word, AlphabetSearch.BaseCorrect entry base word (br word) (ba word) (radius word) := by
  obtain ⟨A, ha⟩ := accepts
  obtain ⟨R, hr⟩ := reaches
  exact ⟨Control A.Label R.Label, inferInstance, .start, code A R, correct radius room br ba A R ha hr⟩

end
end ComplexityOfGenerators.Simulation.SavitchMachine.GraphBase
