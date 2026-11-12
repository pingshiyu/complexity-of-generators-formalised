import ComplexityOfGenerators.Examples.SAT

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

/-- One coin per constant decides whether to introduce the fresh variable.
The sign is the unique one evaluating to that constant under `b`. -/
def Literal.lift (d : ℕ) (b : Bool) (lit : Literal) (replace : Bool) : Literal :=
  match lit with
  | .constant value =>
      if replace then .var (d + 1) (value == b) else .constant value
  | .var j sign => .var j sign

theorem Literal.substitute_lift {d : ℕ} (b : Bool) (lit : Literal)
    (valid : lit.valid d) (replace : Bool) :
    (lit.lift d b replace).substitute (d + 1) b = lit := by
  cases lit with
  | constant value =>
    cases replace <;> cases value <;> cases b <;> simp [lift, substitute]
  | var j sign =>
    have different : j ≠ d + 1 := by have := valid.2; omega
    simp [lift, substitute, different]

theorem Literal.lift_valid {d : ℕ} (b : Bool) (lit : Literal)
    (valid : lit.valid d) (replace : Bool) : (lit.lift d b replace).valid (d + 1) := by
  cases lit with
  | constant value => cases replace <;> simp [lift, Literal.valid]
  | var j sign =>
    exact ⟨valid.1, valid.2.trans (Nat.le_succ d)⟩

/-- Every predecessor is reached by one of the two explicit coin choices. -/
theorem Literal.lift_complete {d : ℕ} (b : Bool) (lit : Literal)
    (valid : lit.valid (d + 1)) :
    ∃ replace, (lit.substitute (d + 1) b).lift d b replace = lit := by
  cases lit with
  | constant value => exact ⟨false, rfl⟩
  | var j sign =>
    by_cases fresh : j = d + 1
    · subst j
      refine ⟨true, ?_⟩
      cases sign <;> cases b <;> simp [substitute, lift]
    · exact ⟨false, by simp [substitute, lift, fresh]⟩

def Clause.lift (d : ℕ) (b : Bool) : Clause → List Bool → Clause
  | [], _ => []
  | lit :: rest, choices =>
      lit.lift d b (choices.headD false) :: Clause.lift d b rest choices.tail

def Formula.lift (d : ℕ) (b : Bool) : Formula → List (List Bool) → Formula
  | [], _ => []
  | c :: rest, choices =>
      Clause.lift d b c (choices.headD []) :: Formula.lift d b rest choices.tail

@[simp] theorem Clause.lift_length (d : ℕ) (b : Bool) (c : Clause) (choices : List Bool) :
    (c.lift d b choices).length = c.length := by
  induction c generalizing choices with
  | nil => rfl
  | cons lit rest ih => simp [lift, ih]

@[simp] theorem Formula.lift_length (d : ℕ) (b : Bool) (f : Formula)
    (choices : List (List Bool)) : (f.lift d b choices).length = f.length := by
  induction f generalizing choices with
  | nil => rfl
  | cons c rest ih => simp [lift, ih]

@[simp] theorem Formula.lift_occurrences (d : ℕ) (b : Bool) (f : Formula)
    (choices : List (List Bool)) : (f.lift d b choices).occurrences = f.occurrences := by
  induction f generalizing choices with
  | nil => rfl
  | cons c rest ih =>
    change (Clause.lift d b c (choices.headD [])).length +
      (Formula.lift d b rest choices.tail).occurrences = c.length + Formula.occurrences rest
    rw [Clause.lift_length, ih]

theorem Clause.substitute_lift {d : ℕ} (b : Bool) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid d) (choices : List Bool) :
    ((c.lift d b choices).map (Literal.substitute (d + 1) b)) = c := by
  induction c generalizing choices with
  | nil => rfl
  | cons lit rest ih =>
    simp only [Clause.lift, List.map_cons]
    rw [lit.substitute_lift b (valid lit (by simp)), ih]
    intro lit hlit
    exact valid lit (by simp [hlit])

theorem Clause.lift_valid {d : ℕ} (b : Bool) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid d) (choices : List Bool) :
    ∀ lit ∈ c.lift d b choices, lit.valid (d + 1) := by
  induction c generalizing choices with
  | nil => simp [lift]
  | cons lit rest ih =>
    intro target member
    rcases List.mem_cons.mp member with equal | member
    · subst target
      exact lit.lift_valid b (valid lit (by simp)) _
    · exact ih (by intro l hl; exact valid l (by simp [hl])) _ target member

theorem Formula.substitute_lift {d : ℕ} (b : Bool) (f : Formula)
    (valid : f.valid d) (choices : List (List Bool)) :
    (f.lift d b choices).substitute (d + 1) b = f := by
  induction f generalizing choices with
  | nil => rfl
  | cons c rest ih =>
    simp only [Formula.lift, Formula.substitute, List.map_cons]
    rw [c.substitute_lift b (valid c (by simp)).2]
    congr 1
    apply ih
    intro c hc
    exact valid c (by simp [hc])

theorem Formula.lift_valid {d : ℕ} (b : Bool) (f : Formula)
    (valid : f.valid d) (choices : List (List Bool)) : (f.lift d b choices).valid (d + 1) := by
  induction f generalizing choices with
  | nil => simp [lift, Formula.valid]
  | cons c rest ih =>
    intro target member
    rcases List.mem_cons.mp member with equal | member
    · subst target
      have good := valid c (by simp)
      refine ⟨?_, c.lift_valid b good.2 _⟩
      intro empty
      have lengths := congrArg List.length empty
      simp only [Clause.lift_length, List.length_nil] at lengths
      exact good.1 (List.length_eq_zero_iff.mp lengths)
    · exact ih (by intro c hc; exact valid c (by simp [hc])) _ target member

theorem Clause.lift_complete {d : ℕ} (b : Bool) (c : Clause)
    (valid : ∀ lit ∈ c, lit.valid (d + 1)) :
    ∃ choices, choices.length = c.length ∧
      Clause.lift d b (c.map (Literal.substitute (d + 1) b)) choices = c := by
  induction c with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons lit rest ih =>
    obtain ⟨replace, head⟩ := lit.lift_complete b (valid lit (by simp))
    obtain ⟨choices, length, tail⟩ := ih (by intro l hl; exact valid l (by simp [hl]))
    exact ⟨replace :: choices, by simp [length], by simp [Clause.lift, head, tail]⟩

theorem Formula.lift_complete {d : ℕ} (b : Bool) (f : Formula)
    (valid : f.valid (d + 1)) :
    ∃ choices, choices.length = f.length ∧
      (f.substitute (d + 1) b).lift d b choices = f := by
  induction f with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons c rest ih =>
    obtain ⟨headChoices, _, head⟩ := Clause.lift_complete b c (valid c (by simp)).2
    obtain ⟨tailChoices, length, tail⟩ := ih (by intro c hc; exact valid c (by simp [hc]))
    exact ⟨headChoices :: tailChoices, by simp [length],
      by simpa [Formula.substitute, Formula.lift, head] using congrArg (c :: ·) tail⟩

/-- The explicit fresh-variable choices have exactly the required inverse
fibre as image; no satisfying predecessor is lost. -/
theorem Formula.lift_image {d : ℕ} (b : Bool) (f : Formula) (valid : f.valid d) :
    {g | ∃ choices, g = f.lift d b choices} =
      {g | g.valid (d + 1) ∧ g.substitute (d + 1) b = f} := by
  ext g
  constructor
  · rintro ⟨choices, rfl⟩
    exact ⟨f.lift_valid b valid choices, f.substitute_lift b valid choices⟩
  · rintro ⟨good, equal⟩
    obtain ⟨choices, _, produces⟩ := g.lift_complete b good
    exact ⟨choices, by simpa [equal] using produces.symm⟩

theorem Formula.lift_satisfiable {d : ℕ} (b : Bool) (f : Formula)
    (valid : f.valid d) (satisfiable : Satisfiable d f) (choices : List (List Bool)) :
    Satisfiable (d + 1) (f.lift d b choices) := by
  apply (satisfiable_prefix d _).mpr
  exact ⟨b, by simpa [f.substitute_lift b valid choices] using satisfiable⟩

theorem Formula.lift_encoding_length {M d : ℕ} (bound : d + 1 ≤ M) (b : Bool)
    (f : Formula) (valid : f.valid d) (choices : List (List Bool)) :
    ((f.lift d b choices).encode M (d + 1)).length = (f.encode M d).length := by
  rw [(f.lift d b choices).encode_length bound (f.lift_valid b valid choices),
    f.encode_length (by omega) valid]
  simp

end ComplexityOfGenerators.Examples.PaddedCNF
