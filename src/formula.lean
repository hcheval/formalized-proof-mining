import types 


inductive formula (ι : Type)  (gri : ground_interpretation ι)
| prime (p : Prop) [decidable p] : formula 
| conjunction : formula → formula → formula
| disjunction : formula → formula → formula
| implication : formula → formula → formula
| universal {σ : type ι gri} : (∥σ∥ → formula) → formula 
| existential {σ : type ι gri} : (∥σ∥ → formula) → formula


inductive restricted_formula (ι : Type)  (gri : ground_interpretation ι)

section basics 

  namespace formula 
  
  infixr `⟹` : 45 := implication
  infix `⋀` : 50 := conjunction 
  infix `⋁` : 50 := disjunction 
  notation `universal'` := @universal _ _ 
  notation `existential'` := @existential _ _ 
  -- how does this actually work?
  notation `∀∀` binders `,` r:(scoped A, universal A) := r
  notation `∃∃` binders  `,` r:(scoped A, existential A) := r  

  @[reducible, simp] def falsum (ι : Type) (gri : ground_interpretation ι) : formula ι gri := @prime ι gri false _
  @[reducible, simp] def falsum' {ι : Type} {gri : ground_interpretation ι} : formula ι gri := falsum _ _

  variables {ι : Type} {gri : ground_interpretation ι}

  local notation `𝕋` := type ι gri
  local notation `𝔽` := formula ι gri

  instance : has_bot 𝔽 := ⟨falsum ι gri⟩


  def negation (A : 𝔽) := A ⟹ falsum ι gri
  prefix `∼` : 90 := negation 

  def equivalence (A B : 𝔽) := A ⟹ B ⋀ B ⟹ A
  infixl `⇔` : 15 := equivalence
  
  @[simp]
  def eqext (greq : Π {i : ι}, ∥𝕏 i∥ → ∥𝕏 i∥ → 𝔽) : Π {σ : 𝕋}, ∥σ∥ → ∥σ∥ → 𝔽 
  | 𝕆 x y := prime $ x = y
  | (𝕏 i) x y := greq x y
  | (σ ↣ τ) x y := ∀∀ z : ∥σ∥ , (eqext (x z) (y z))
  | (σ ⊗ τ) x y := eqext x.1 y.1 ⋀ eqext x.2 y.2

  @[simp, pp_nodot]
  def interpret : 𝔽 → Prop 
  | (@prime _ _ p _) := p
  | (A ⋀ B) := A.interpret ∧ B.interpret 
  | (A ⋁ B) := A.interpret ∨ B.interpret 
  | (A ⟹ B) := A.interpret → B.interpret 
  | (universal' σ A) := ∀ x : ∥σ∥, (A x).interpret
  | (existential' σ A) := ∃ x : ∥σ∥, (A x).interpret

  -- @[simp]
  -- lemma prime_interpret (p : Prop) [decidable p] : ∥(prime p : 𝔽)∥ ↔ p := 
  -- by split; intros; simpa

  notation `∥` A `∥` := interpret A

  end formula

end basics

section kinds_of_formulas 

  variables {ι : Type}  {gri : ground_interpretation ι}
  local notation `𝕋` := type ι gri
  local notation `𝔽` := formula ι gri 
  variables {greq : Π {i : ι}, ∥𝕏 i // gri∥ → ∥𝕏 i // gri∥ → 𝔽}

  namespace formula 

  @[simp]
  def is_qf : 𝔽 → Prop 
  | (@prime _ _ _ _) := true
  | (A ⋀ B) := and A.is_qf B.is_qf
  | (A ⋁ B) := and A.is_qf B.is_qf
  | (A ⟹ B) := and A.is_qf B.is_qf
  | (universal' σ A) := false
  | (existential' σ A) := false

  @[simp]
  def is_qf_disj_free : 𝔽 → Prop 
  | (@prime _ _ _ _) := true
  | (A ⋀ B) := and A.is_qf_disj_free B.is_qf_disj_free
  | (A ⋁ B) := false
  | (A ⟹ B) := and A.is_qf_disj_free B.is_qf_disj_free
  | (universal' σ A) := false
  | (existential' σ A) := false

  inductive purely_univ : 𝔽 → Type
  | of_qf (A : 𝔽) : A.is_qf → purely_univ A
  | of_univ {σ : 𝕋} (A : ∥σ∥ → 𝔽) : (∀ x : ∥σ∥, purely_univ (A x)) → purely_univ (universal' σ A)

  def is_purely_univ : 𝔽 → Prop 
  | (@prime _ _ _ _) := true
  | (A ⋀ B) := A.is_qf ∧ B.is_qf
  | (A ⋁ B) := A.is_qf ∧ B.is_qf
  | (A ⟹ B) := A.is_qf ∧ B.is_qf
  | (universal' σ A) := ∀ x, is_purely_univ (A x)
  | (existential' σ A) := false

  inductive purely_univ_disj_free : 𝔽 → Type
  | of_qf_disj_free (A : 𝔽) : A.is_qf_disj_free → purely_univ_disj_free A
  | of_univ {σ : 𝕋} (A : ∥σ∥ → 𝔽) : (∀ x : ∥σ∥, purely_univ_disj_free (A x)) → purely_univ_disj_free (universal' σ A)

  

  end formula 

end kinds_of_formulas




