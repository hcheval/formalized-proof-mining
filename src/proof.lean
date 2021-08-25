import formula 
import dialectica
import utils


section basics

  variables {ι : Type} {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables (greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽)
  local infixr `≅` : 35 := formula.eqext @greq


  structure principles := 
  (with_lem : bool := ff)
  (with_markov : bool := ff)
  (with_ip : bool := ff)
  (with_ac : bool := ff)

  @[reducible]
  def plain : principles := {}

  -- structure premises (ι : Type) (gri : ground_interpretation ι) := 
  -- (formulas : list $ formula ι gri)
  -- (realizable : Π {γ : formula ι gri}, γ ∈ formulas → dia.realizer γ)

  @[reducible]
  def premises (ι : Type) (gri : ground_interpretation ι) := list $ formula ι gri

  @[reducible] 
  def premises' {ι : Type} {gri : ground_interpretation ι} := premises ι gri
  

  -- instance : has_mem (formula ι gri) (premises ι gri) := ⟨λ A Γ, A ∈ Γ.formulas⟩

  open formula 

  inductive proof 
    (extra : principles)
    (Γ : list $ formula ι gri)
    : 𝔽 → Type
  -- `id` bug
  | qfer (σ : 𝕋) (x y : ∥σ∥) (A : ∥σ∥ → 𝔽) : 
    proof (x ≅ y) → proof (A (id x) ⟹ A (id y))
  | and_contr (A : 𝔽) : proof (A ⟹ A ⋀ A)
  | or_contr (A : 𝔽) : proof (A ⋁ A ⟹ A)
  | and_weak (A B : 𝔽) : proof (A ⋀ B ⟹ A)
  | or_weak (A B : 𝔽) : proof (A ⟹ A ⋁ B)
  | and_perm (A B : 𝔽) : proof (A ⋀ B ⟹ B ⋀ A)
  | or_perm (A B : 𝔽) : proof (A ⋁ B ⟹ B ⋁ A)
  | exfalso  (A : 𝔽) : proof (prime false ⟹ A)
  | univ_ax {σ : 𝕋} (A : ∥σ∥ → 𝔽) : Π x, proof (universal' σ A ⟹ A x)
  | exist_ax {σ : 𝕋} (A : ∥σ∥ → 𝔽) : Π x, proof (A x ⟹ existential' σ A)
  | mp {A B : 𝔽} : proof A → proof (A ⟹ B) → proof B 
  | syl {A B C : 𝔽} : proof (A ⟹ B) → proof (B ⟹ C) → proof (A ⟹ C)
  | importation {A B C : 𝔽} : proof (A ⟹ B ⟹ C) → proof (A ⋀ B ⟹ C)
  | exportation {A B C : 𝔽} : proof (A ⋀ B ⟹ C) → proof (A ⟹ B ⟹ C)
  | expansion {A B C : 𝔽} : proof (A ⟹ B) → proof (C ⋁ A ⟹ C ⋁ B)
  | univ_rule {σ : 𝕋} {A : 𝔽} {B : ∥σ∥ → 𝔽} : (Π x : ∥σ∥, proof (A ⟹ B x)) → proof (A ⟹ universal' σ B)
  | exist_rule {σ : 𝕋} {A : 𝔽} {B : ∥σ∥ → 𝔽} : (Π x : ∥σ∥, proof (B x ⟹ A)) → proof (existential' σ B ⟹ A)
  | ir {A : ∥𝕆 // gri∥ → 𝔽} (m : ℕ) : proof (A 0) → (Π (n : ℕ), proof (A n ⟹ A n.succ)) → proof (A m)
  | lem (A : 𝔽) : extra.with_lem → proof (A ⋁ ∼A)
  | markov {σ : 𝕋} {A : ∥σ∥ → 𝔽} [∀ x, subsingleton (A x).𝕎] [∀ x, subsingleton (A x).ℂ] : extra.with_markov → 
    proof (∼(∀∀ (x : ∥σ∥) , ∼(A x)) ⟹ (∃∃ (x : ∥σ∥) , A x))
  | ip {σ τ : 𝕋} {A : ∥σ∥ → 𝔽} {B : ∥τ∥ → 𝔽} 
    [∀ x : ∥σ∥, subsingleton (A x).𝕎] [∀ y : ∥τ∥, subsingleton (B y).ℂ] : extra.with_ip →
    proof (((∀∀ (x : ∥σ∥) , A x) ⟹ (∃∃ (y : ∥τ∥) , B y)) ⟹ ∃∃ (y : ∥τ∥) , ((∀∀ (x : ∥σ∥) , A x) ⟹ B y))
  | ac {σ τ : 𝕋} (A : ∥σ∥ → ∥τ∥ → 𝔽) : extra.with_ac → 
    proof ((∀∀ (x : ∥σ∥) , (∃∃ (y : ∥τ∥) , A x y)) ⟹ ∃∃ (Y : ∥σ ↣ τ∥) , ∀∀ (x : ∥σ∥) , A x (Y x))
  | premise (A : 𝔽) : A ∈ Γ → proof A
  | of_prime_true {p : Prop} [decidable p] : p → proof (prime p)


end basics

section basics 

  variables {ι : Type}  {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq
  variables {extra : principles} {Γ : premises ι gri} {A B : 𝔽}

  namespace proof 

  @[reducible, simp] def and_contr' {A : 𝔽} := @and_contr ι gri @greq extra Γ A 
  @[reducible, simp] def or_contr' {A : 𝔽} := @or_contr ι gri @greq extra Γ A
  @[reducible, simp] def and_weak' {A B : 𝔽} := @and_weak ι gri @greq extra Γ A B
  @[reducible, simp] def or_weak' {A B : 𝔽} := @or_weak ι gri @greq extra Γ A B
  @[reducible, simp] def and_perm' {A B : 𝔽} := @and_perm ι gri @greq extra Γ A B 
  @[reducible, simp] def or_perm' {A B : 𝔽} := @or_perm ι gri @greq extra Γ A B
  @[reducible, simp] def exfalso' {A : 𝔽} := @exfalso ι gri @greq extra Γ A
  @[reducible, simp] def univ_ax' {σ : 𝕋} {A : ∥σ∥ → 𝔽} {x : ∥σ∥} := @univ_ax ι gri @greq extra Γ σ A x
  @[reducible, simp] def exist_ax' {σ : 𝕋} {A : ∥σ∥ → 𝔽} {x : ∥σ∥} := @exist_ax ι gri @greq extra Γ σ A x


  end proof

end basics 


section schemata 

  variables {ι : Type} [decidable_eq ι] {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq
  variables {Γ : premises ι gri}


  namespace proof 

  local infix `⊢` : 10 := proof @greq plain 

  section substitution_of_equivalents 

    -- variables {A B P : 𝔽}

    -- def subst_equiv (i : ℕ) : (Γ ⊢ A ⇔ B) → (Γ ⊢ P.substitute i A ⇔ P.substitute i A) 

    variables {A B : 𝔽} {P : 𝔽 → 𝔽}

    def subst_equiv (i : ℕ) : (Γ ⊢ A ⇔ B) → (Γ ⊢ P A ⇔ P B) := sorry


  end substitution_of_equivalents
  
  section propositional

    variables {A B : 𝔽}

    def A_imp_A : (Γ ⊢ A ⟹ A) := 
      syl and_contr' and_weak'

    def A_imp_B_imp_A : (Γ ⊢ A ⟹ (B ⟹ A)) := 
      exportation and_weak' 


    section double_negation 

      def qf_lem (qfA : A.is_qf) : (Γ ⊢ A ⋁ ∼A) := 
      begin 
            
      end

      def A_imp_neg_neg_A : (Γ ⊢ A ⟹ ∼∼A) := sorry 

      def neg_neg_lem : (Γ ⊢ ∼∼(A ⋁ ∼A)) := sorry 

      def neg_neg_conj : (Γ ⊢ ∼∼(A ⋀ B) ⇔ ∼∼A ⋀ ∼∼B) := sorry 

      def neg_neg_imp : (Γ ⊢ ∼∼(A ⟹ B) ⇔ ∼∼A ⟹ ∼∼B) := sorry 




    end double_negation


  end propositional


  section first_order 

    open formula 

    variables {σ τ : 𝕋} {A : ∥σ∥ → 𝔽} {B : ∥σ∥ → 𝔽}

    def univ_imp_exist : (Γ ⊢ universal A ⟹ existential A) := 
      syl univ_ax' (exist_ax _ σ.inh)
    -- we need an inhabitant
    -- remark, when doing this proof on paper you actually assume an inhabitant to exist

    


  end first_order


  end proof

end schemata