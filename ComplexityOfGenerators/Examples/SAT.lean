import ComplexityOfGenerators.SelfReducibility

/-!
# The concrete padded CNF encoding from the manuscript

This module supplies the semantic part of the SAT example: concrete literals,
the padded word encoding, substitution, and the exact certificate-prefix law.
It does not postulate native machines or assert exact recursive generability.
The later parser, self-reduction, ancestor and inverse-word modules prove the
codec and all-word semantic laws. Native rank and width transducers are supplied in `SATHeaderMachines` and
`SATComputability`; `SATNative` supplies the full all-word native parser and
polynomial certificate verifier, checked substitution and complete native
constant-formula base sampler. `SATNative.PolynomialReduction` assembles the
actual native `PolynomialSelfReduction`. `SATNative.ExactRecursive` combines
this with the concrete base and fresh-variable inverse generators, proving
`ExactlyRecursivelyGenerable` and native polynomial generability.
-/

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

inductive Symbol
  | zero | one | separator | trueConstant | falseConstant
  | positive | negative | openClause | closeClause
  deriving DecidableEq, Fintype

inductive Literal
  | constant (value : Bool)
  | var (index : ℕ) (positive : Bool)
  deriving DecidableEq

abbrev Clause := List Literal
abbrev Formula := List Clause
abbrev Assignment := ℕ → Bool

def Literal.eval (a : Assignment) : Literal → Bool
  | .constant b => b
  | .var j positive => if positive then a j else !(a j)

def Clause.eval (a : Assignment) (c : Clause) : Bool := c.any (Literal.eval a)
def Formula.eval (a : Assignment) (f : Formula) : Bool := f.all (Clause.eval a)

def Literal.valid (d : ℕ) : Literal → Prop
  | .constant _ => True
  | .var j _ => 0 < j ∧ j ≤ d

def Formula.valid (d : ℕ) (f : Formula) : Prop :=
  ∀ c ∈ f, c ≠ [] ∧ ∀ lit ∈ c, lit.valid d

def Literal.encode (M : ℕ) : Literal → List Symbol
  | .constant b => [if b then .trueConstant else .falseConstant] ++
      List.replicate M .zero
  | .var j positive => [if positive then .positive else .negative] ++
      List.replicate j .one ++ List.replicate (M - j) .zero

def Clause.encode (M : ℕ) (c : Clause) : List Symbol :=
  [.openClause] ++ c.flatMap (Literal.encode M) ++ [.closeClause]

def Formula.encode (M d : ℕ) (f : Formula) : List Symbol :=
  List.replicate M .one ++ [.separator] ++ List.replicate d .one ++
    List.replicate (M - d) .zero ++ [.separator] ++ f.flatMap (Clause.encode M)

def Formula.occurrences (f : Formula) : ℕ := (f.map List.length).sum

theorem Literal.encode_length {M d : ℕ} (bound : d ≤ M) (lit : Literal)
    (valid : lit.valid d) : (lit.encode M).length = M + 1 := by
  cases lit with
  | constant b => simp [encode]
  | var j sign =>
    have hj := valid.2.trans bound
    simp only [encode, List.length_append, List.length_singleton, List.length_replicate]
    omega

theorem Clause.encode_length {M d : ℕ} (bound : d ≤ M) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid d) :
    (c.encode M).length = 2 + (M + 1) * c.length := by
  have body : (c.flatMap (Literal.encode M)).length = (M + 1) * c.length := by
    induction c with
    | nil => simp
    | cons lit rest ih =>
      rw [List.flatMap_cons, List.length_append,
        lit.encode_length bound (valid lit (by simp)), ih]
      · simp [Nat.mul_add]; omega
      · intro x hx; exact valid x (by simp [hx])
  simp [Clause.encode, body]
  omega

theorem Formula.encode_length {M d : ℕ} (bound : d ≤ M) (f : Formula)
    (valid : f.valid d) :
    (f.encode M d).length = 2 * M + 2 + 2 * f.length + (M + 1) * f.occurrences := by
  have body : (f.flatMap (Clause.encode M)).length =
      2 * f.length + (M + 1) * f.occurrences := by
    induction f with
    | nil => simp [occurrences]
    | cons c rest ih =>
      rw [List.flatMap_cons, List.length_append,
        c.encode_length bound (valid c (by simp)).2, ih]
      · simp [occurrences, Nat.mul_add]; omega
      · intro c hc; exact valid c (by simp [hc])
  simp only [Formula.encode, List.length_append, List.length_replicate,
    List.length_singleton, body]
  omega

def Literal.substitute (j : ℕ) (b : Bool) : Literal → Literal
  | .constant value => .constant value
  | .var index sign =>
      if index = j then .constant (if sign then b else !b) else .var index sign

def Formula.substitute (j : ℕ) (b : Bool) (f : Formula) : Formula :=
  f.map (List.map (Literal.substitute j b))

theorem Literal.eval_substitute (a : Assignment) (j : ℕ) (b : Bool) (lit : Literal) :
    (lit.substitute j b).eval a = lit.eval (Function.update a j b) := by
  cases lit with
  | constant value => rfl
  | var index sign =>
    by_cases h : index = j
    · subst index; simp [substitute, eval]
    · simp [substitute, eval, h]

theorem Formula.eval_substitute (a : Assignment) (j : ℕ) (b : Bool) (f : Formula) :
    (f.substitute j b).eval a = f.eval (Function.update a j b) := by
  simp only [Formula.substitute, Formula.eval, List.all_map]
  congr 1
  funext c
  simp only [Function.comp_apply, Clause.eval, List.any_map]
  congr 1
  funext lit
  exact lit.eval_substitute a j b

theorem Literal.valid_substitute {d : ℕ} (b : Bool) (lit : Literal)
    (valid : lit.valid (d + 1)) : (lit.substitute (d + 1) b).valid d := by
  cases lit with
  | constant value => trivial
  | var j sign =>
    by_cases h : j = d + 1
    · simp [substitute, h, Literal.valid]
    · simpa [substitute, h, Literal.valid] using
        (show 0 < j ∧ j ≤ d from ⟨valid.1, by have := valid.2; omega⟩)

theorem Formula.valid_substitute {d : ℕ} (b : Bool) (f : Formula)
    (valid : f.valid (d + 1)) : (f.substitute (d + 1) b).valid d := by
  intro c hc
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp hc
  have good := valid original member
  constructor
  · simpa using good.1
  · intro lit hlit
    obtain ⟨originalLit, memberLit, rfl⟩ := List.mem_map.mp hlit
    exact originalLit.valid_substitute b (good.2 originalLit memberLit)

@[simp] theorem Formula.substitute_length (j : ℕ) (b : Bool) (f : Formula) :
    (f.substitute j b).length = f.length := by simp [substitute]

@[simp] theorem Formula.substitute_occurrences (j : ℕ) (b : Bool) (f : Formula) :
    (f.substitute j b).occurrences = f.occurrences := by
  simp [substitute, occurrences, List.map_map, Function.comp_def]

theorem Formula.substitute_encoding_length {M d : ℕ} (bound : d + 1 ≤ M)
    (b : Bool) (f : Formula) (valid : f.valid (d + 1)) :
    ((f.substitute (d + 1) b).encode M d).length = (f.encode M (d + 1)).length := by
  rw [(f.substitute (d + 1) b).encode_length (by omega) (f.valid_substitute b valid),
    f.encode_length bound valid]
  simp

/-- The first bit assigns the last active variable, exactly as in the paper. -/
def assignment : List Bool → Assignment
  | [] => fun _ => false
  | b :: rest => Function.update (assignment rest) (rest.length + 1) b

def certificates (d : ℕ) (f : Formula) : Set (List Bool) :=
  {c | c.length = d ∧ f.eval (assignment c) = true}

def Satisfiable (d : ℕ) (f : Formula) : Prop := (certificates d f).Nonempty

/-- The manuscript's actual word language, including its capacity header and
the padded fixed-width literal records. -/
def language : Language Symbol :=
  {word | ∃ M d f, d ≤ M ∧ f.valid d ∧ Satisfiable d f ∧ f.encode M d = word}

theorem certificate_prefix (d : ℕ) (f : Formula) (c : List Bool) :
    c ∈ certificates (d + 1) f ↔
      ∃ b rest, c = b :: rest ∧ rest ∈ certificates d (f.substitute (d + 1) b) := by
  cases c with
  | nil => simp [certificates]
  | cons b rest =>
    constructor
    · intro hc
      have len : rest.length = d := by have := hc.1; simp at this; omega
      refine ⟨b, rest, rfl, len, ?_⟩
      rw [Formula.eval_substitute]
      simpa [assignment, len] using hc.2
    · rintro ⟨b', rest', eq, hc⟩
      have equal : b = b' ∧ rest = rest' := List.cons.inj eq
      rcases equal with ⟨rfl, rfl⟩
      refine ⟨by simp [hc.1], ?_⟩
      have evaluate := hc.2
      rw [Formula.eval_substitute] at evaluate
      simpa [assignment, hc.1] using evaluate

theorem satisfiable_prefix (d : ℕ) (f : Formula) :
    Satisfiable (d + 1) f ↔ ∃ b, Satisfiable d (f.substitute (d + 1) b) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, rest, _, hr⟩ := (certificate_prefix d f c).mp hc
    exact ⟨b, rest, hr⟩
  · rintro ⟨b, c, hc⟩
    exact ⟨b :: c, (certificate_prefix d f (b :: c)).mpr ⟨b, c, rfl, hc⟩⟩

theorem certificates_zero (f : Formula) :
    certificates 0 f = {c | c = [] ∧ f.eval (fun _ => false) = true} := by
  ext c
  simp only [certificates, Set.mem_ofPred_eq, List.length_eq_zero_iff]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩

end ComplexityOfGenerators.Examples.PaddedCNF
