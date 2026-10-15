import ComplexityOfGenerators.Simulation.SavitchMachine.Root
import ComplexityOfGenerators.Simulation.SavitchMachine.InitialVertex
import ComplexityOfGenerators.Simulation.SavitchMachine.Ruler
import ComplexityOfGenerators.Simulation.StackSpace.Transport

/-! Uniform input initialization for Savitch's interpreter: preserve the input,
compute the two polynomial rulers, build the native initial-configuration code,
and assemble the root frame. Every loop is part of one finite control table. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Initialize

open Turing StackSpace Frames Complexity
set_option backward.isDefEq.respectTransparency false

inductive Label (spaceDegree depthDegree : ℕ)
  | load
  | space (pc : Ruler.Label spaceDegree)
  | vertex (pc : InitialVertex.Label)
  | depth (pc : Ruler.Label depthDegree)
  | clear | reset
  | root (pc : Root.Label)
  deriving DecidableEq, Fintype

def spaceSlots : Fin 5 ↪ Fin 13 := ⟨![12, 0, 1, 2, 3], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
def vertexSlots : Fin 6 ↪ Fin 13 := ⟨![0, 1, 2, 3, 4, 9], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
def depthSlots : Fin 5 ↪ Fin 13 := ⟨![12, 8, 0, 1, 2], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
def rootSlots : Fin 12 ↪ Fin 13 := ⟨Fin.castSucc, fun _ _ h => Fin.castSucc_inj.mp h⟩

variable {S : Type} [Inhabited S]

def pack (write : Symbol → S) (v : Local) : Status × Option S := (v.1, v.2.map write)
def unpack (read : S → Symbol) (v : Status × Option S) : Local := (v.1, v.2.map read)

theorem pack_inverse (write : Symbol → S) (read : S → Symbol) (inverse : Function.LeftInverse read write) :
    Function.LeftInverse (unpack read) (pack write) := by
  rintro ⟨status, cache⟩
  cases cache with
  | none => rfl
  | some symbol => simp [pack, unpack, inverse symbol]

abbrev unary (write : Symbol → S) (n : ℕ) : List S := List.replicate n (write (some false))

variable (write : Symbol → S) (read : S → Symbol)

def program (state : List Bool) (symbols : ℕ) (space depth : PolynomialBound) :
    Label space.degree depth.degree → Stmt S (Label space.degree depth.degree) (Status × Option S) 12
  | .load => transferCode 0 12 .load (.space .copyInput) (fun _ => true)
  | .space .finish => .goto fun _ => .vertex .seed
  | .space pc => embedCode spaceSlots Label.space (Ruler.program (write (some false)) space pc)
  | .vertex .done => .goto fun _ => .depth .copyInput
  | .vertex pc => embedCode vertexSlots Label.vertex (transportCode write read (pack write) (unpack read) (InitialVertex.program state symbols pc))
  | .depth .finish => .goto fun _ => .clear
  | .depth pc => embedCode depthSlots Label.depth (Ruler.program (write (some false)) depth pc)
  | .clear => clearCode 0 .clear .reset (fun _ => true)
  | .reset => .load (fun _ => (status ⟨false, false, none, []⟩, none)) (.goto fun _ => .root .seed)
  | .root pc => embedCode rootSlots Label.root (transportCode write read (pack write) (unpack read) (Root.program pc))

def radius (state : List Bool) (symbols : ℕ) (space depth : PolynomialBound) (n : ℕ) : ℕ :=
  n + space n + depth n + InitialVertex.radius state symbols n (space n) +
    depth n + (InitialVertex.code state symbols n (space n)).length + 10

theorem run (inverse : Function.LeftInverse read write) (state : List Bool) (symbols : ℕ) (space depth : PolynomialBound) (word : List S) :
    Trace (program write read state symbols space depth) (radius state symbols space depth word.length)
      (sourceInitial .load (carrying false false, none) word)
      (extendConfig word (localConfig (.root .done) (status ⟨false, false, none, []⟩)
        (fun j => (memory [Root.frame (depth word.length) (InitialVertex.code state symbols word.length (space word.length))]
          (fun _ => []) j).map write))) := by
  let P := program write read state symbols space depth
  let r := radius state symbols space depth word.length
  let v := carrying false false
  let code := InitialVertex.code state symbols word.length (space word.length)
  let loaded : Fin 13 → List S := ![[], [], [], [], [], [], [], [], [], [], [], [], word]
  have initial : ∀ j, (inputStacks (k := 12) word j).length ≤ r := by
    intro j
    simp [inputStacks, Function.update_apply]
    split_ifs <;> simp [r, radius] <;> omega
  have load := transfer_all P 0 12 (by decide) .load (.space .copyInput) (fun _ => true) rfl
    v (inputStacks (k := 12) word) (by simp) r initial (by simp [inputStacks, r, radius] <;> omega)
  have loadMemory : replaceTwo (inputStacks (k := 12) word) (0 : Fin 13) 12 []
      ((inputStacks (k := 12) word 0).reverse ++ inputStacks (k := 12) word 12) = loaded := by
    funext j; fin_cases j <;> simp [inputStacks, replaceTwo, loaded, Function.update_apply]
  rw [loadMemory] at load
  have ruler := ((Ruler.run_with (write (some false)) space v word).mono
    (show word.length + space word.length + 1 ≤ r by dsimp [r, radius]; omega)).embed_active
    (by simp [localConfig]) spaceSlots Label.space P
    (by intro pc nonhalt; cases pc <;> first | rfl | exact False.elim (nonhalt rfl)) loaded load.end_bound
  let measured : Fin 13 → List S :=
    ![unary write (space word.length), unary write (word.length + 1), [], [], [], [], [], [], [], [], [], [], word]
  have rulerBefore : Function.extend spaceSlots ![word, [], [], [], []] loaded = loaded := by
    apply extend_eq
    · intro j; fin_cases j <;> rfl
    · intro j _; rfl
  have rulerAfter : Function.extend spaceSlots
      ![word, unary write (space word.length), unary write (word.length + 1), [], []] loaded = measured := by
    apply extend_eq
    · intro j; fin_cases j <;> rfl
    · intro j outside; fin_cases j <;> simp_all [spaceSlots, Fin.exists_fin_succ, measured, loaded]
  rw [embed_local spaceSlots Label.space loaded loaded _ _ v rulerBefore,
    embed_local spaceSlots Label.space loaded measured _ _ v rulerAfter] at ruler
  have beginVertex : TM2.step P (localConfig (.space .finish) v measured) =
      some (localConfig (.vertex .seed) v measured) := rfl
  have vertex := ((Trace.transport write read (pack write) (unpack read) inverse (pack_inverse write read inverse)
      (InitialVertex.build state symbols word.length (space word.length))).mono
    (show InitialVertex.radius state symbols word.length (space word.length) ≤ r by dsimp [r, radius]; omega)).embed_active
    (by simp [localConfig, transportConfig]) vertexSlots Label.vertex P
    (by intro pc nonhalt; cases pc <;> first | rfl | exact False.elim (nonhalt rfl)) measured ruler.end_bound
  let built : Fin 13 → List S := ![[], [], [], [], [], [], [], [], [], code.reverse.map (write ∘ some), [], [], word]
  have vertexBefore : Function.extend vertexSlots
      (fun j => (![CoordinateEncode.unary (space word.length), CoordinateEncode.unary (word.length + 1), [], [], [], []] j).map write) measured = measured := by
    apply extend_eq
    · intro j; fin_cases j <;> simp [vertexSlots, measured, CoordinateEncode.unary, unary]
    · intro j _; rfl
  have vertexAfter : Function.extend vertexSlots
      (fun j => (![([] : List Symbol), [], [], [], [], code.reverse.map some] j).map write) measured = built := by
    apply extend_eq
    · intro j; fin_cases j <;> simp [vertexSlots, built]
    · intro j outside; fin_cases j <;> simp_all [vertexSlots, Fin.exists_fin_succ, measured, built]
  simp only [embedConfig, transportConfig, localConfig, pack, Option.map_none, Option.map_some] at vertex
  rw [vertexBefore, vertexAfter] at vertex
  have beginDepth : TM2.step P (localConfig (.vertex .done) v built) =
      some (localConfig (.depth .copyInput) v built) := rfl
  have depthRuler := ((Ruler.run_with (write (some false)) depth v word).mono
    (show word.length + depth word.length + 1 ≤ r by dsimp [r, radius]; omega)).embed_active
    (by simp [localConfig]) depthSlots Label.depth P
    (by intro pc nonhalt; cases pc <;> first | rfl | exact False.elim (nonhalt rfl)) built vertex.end_bound
  let withDepth : Fin 13 → List S :=
    ![unary write (word.length + 1), [], [], [], [], [], [], [], unary write (depth word.length), code.reverse.map (write ∘ some), [], [], word]
  have depthBefore : Function.extend depthSlots ![word, [], [], [], []] built = built := by
    apply extend_eq
    · intro j; fin_cases j <;> rfl
    · intro j _; rfl
  have depthAfter : Function.extend depthSlots
      ![word, unary write (depth word.length), unary write (word.length + 1), [], []] built = withDepth := by
    apply extend_eq
    · intro j; fin_cases j <;> rfl
    · intro j outside; fin_cases j <;> simp_all [depthSlots, Fin.exists_fin_succ, built, withDepth]
  rw [embed_local depthSlots Label.depth built built _ _ v depthBefore,
    embed_local depthSlots Label.depth built withDepth _ _ v depthAfter] at depthRuler
  have beginClear : TM2.step P (localConfig (.depth .finish) v withDepth) =
      some (localConfig .clear v withDepth) := rfl
  have clear := clear_all P 0 .clear .reset (fun _ => true) rfl v withDepth (by simp) r depthRuler.end_bound
  let prepared : Fin 13 → List S := Fin.snoc (α := fun _ => List S) (fun j => (Root.prepared (depth word.length) code j).map write) word
  have cleared : Function.update withDepth (0 : Fin 13) [] = prepared := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · dsimp only [prepared]
      rw [Fin.snoc_last]
      rfl
    · dsimp only [prepared]
      rw [Fin.snoc_castSucc]
      fin_cases i <;> simp [withDepth, Root.prepared, Function.update_apply, unary]
  rw [cleared] at clear
  let initialStatus := status ⟨false, false, none, []⟩
  have reset : TM2.step P (localConfig .reset v prepared) =
      some (localConfig (.root .seed) initialStatus prepared) := rfl
  have root := ((Trace.transport write read (pack write) (unpack read) inverse (pack_inverse write read inverse)
      (Root.assemble (depth word.length) code)).mono
    (show depth word.length + code.length + 2 ≤ r by dsimp [code, r, radius]; omega)).embed_active
    (by simp [localConfig, transportConfig]) rootSlots Label.root P (fun _ _ => rfl) prepared clear.end_bound
  have rootBefore : Function.extend rootSlots (fun j => (Root.prepared (depth word.length) code j).map write) prepared = prepared := by
    apply extend_eq
    · intro j
      simp only [rootSlots, Function.Embedding.coeFn_mk, prepared, Fin.snoc_castSucc]
    · intro j _; rfl
  have rootAfter : Function.extend rootSlots (fun j => (memory [Root.frame (depth word.length) code] (fun _ => []) j).map write) prepared =
      Fin.snoc (α := fun _ => List S) (fun j => (memory [Root.frame (depth word.length) code] (fun _ => []) j).map write) word := by
    apply extend_eq
    · intro j
      simp only [rootSlots, Function.Embedding.coeFn_mk, Fin.snoc_castSucc]
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · intro _; simp [prepared, Fin.snoc]
      · intro outside; exact False.elim (outside ⟨i, rfl⟩)
  simp only [embedConfig, transportConfig, localConfig, pack, Option.map_none, Option.map_some] at root
  rw [rootBefore, rootAfter] at root
  have path := load.trans ruler
  have path := path.trans (.step ruler.end_bound beginVertex vertex)
  have path := path.trans (.step vertex.end_bound beginDepth depthRuler)
  have path := path.trans (.step depthRuler.end_bound beginClear clear)
  exact path.trans (.step clear.end_bound reset root)

/-- A uniform polynomial bound for every initialization phase, including
copies, intermediate binary increments, and the completed root frame. -/
noncomputable def spaceBound (state : List Bool) (symbols : ℕ) (space depth : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (Polynomial.C (2 * state.length + 24) + 5 * Polynomial.X +
    9 * space.asPolynomial + 2 * depth.asPolynomial +
    2 * Polynomial.C (symbols + 1) * (2 * space.asPolynomial + 1))

theorem radius_le_spaceBound (state : List Bool) (symbols : ℕ) (space depth : PolynomialBound) (n : ℕ) :
    radius state symbols space depth n ≤ spaceBound state symbols space depth n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (Polynomial.C (2 * state.length + 24) + 5 * Polynomial.X +
      9 * space.asPolynomial + 2 * depth.asPolynomial +
      2 * Polynomial.C (symbols + 1) * (2 * space.asPolynomial + 1)) n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval] at bound
  have exactSize : radius state symbols space depth n =
      2 * state.length + 24 + 5 * n + 9 * space n + 2 * depth n +
        2 * (symbols + 1) * (2 * space n + 1) := by
    simp only [radius, InitialVertex.radius, InitialVertex.code_length]
    ring
  rw [exactSize]
  exact bound


end ComplexityOfGenerators.Simulation.SavitchMachine.Initialize
