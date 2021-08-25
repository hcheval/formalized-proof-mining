import dialectica 
import proof
import realizers
import majorizability
import data.equiv.basic

section 

  parameters {ι : Type} {gri : ground_interpretation ι}
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq
  

  
  open formula (𝕎_inh' ℂ_inh')
  set_option pp.proofs true 
  def metatheorem 
    (𝕄 : 𝕋 → 𝕋) [maj_type 𝕄] (maj : majorizability 𝕄) (admissible : admissible_greq @greq)
    (σ : 𝕋) (A B : ∥𝕆 // gri∥ → ∥σ∥ → 𝔽)
    (trivialA : ∀ a b x y, (A a b).dia x y ↔ ∥A a b∥)
    (trivialB : ∀ a b x y, (B a b).dia x y ↔ ∥B a b∥)
    (Γ : premises')
    (premise_realizer : Π {γ : 𝔽}, γ ∈ Γ → dia.realizer γ) 
    (prf : proof @greq {with_markov := tt, with_ip := tt} Γ $ ∀∀ x : ∥σ∥, ((∀∀ u : ∥𝕆∥, A u x) ⟹ (∃∃v : ∥𝕆∥, B v x))) :
    {φ : ∥𝕄 σ∥ → ℕ // ∀ (x : ∥σ∥) (x' : ∥𝕄 σ∥) (_ : maj.majorizes x x'), (∀ u : ℕ, u ≤ φ x' → ∥A u x∥) → (∃ v : ℕ, v ≤ φ x' ∧ ∥B v x∥)}
    := 
    let ⟨t, h⟩ := prf.dia_realize admissible @premise_realizer in
    let y : ∥σ∥ → (Σ (x : ∥σ∥), (Π (x_1 : ℕ), (A x_1 x).mwc.fst) × Π (x_1 : ℕ), (B x_1 x).mwc.fst → (B x_1 x).mwc.snd) 
      := λ x, sigma.mk x ⟨(λ _, 𝕎_inh'), (λ _ _, ℂ_inh')⟩ in
    let t₁ : ∥σ∥ → ℕ := λ x, ((t x).1 (λ _, 𝕎_inh') (λ _ _, ℂ_inh')).1 in
    let t₂ : ∥σ∥ → ℕ := λ x, ((t x).2 (λ _, 𝕎_inh')).1 in
    have h' : (∥σ∥ → ℕ) = ∥σ ↣ 𝕆∥ := rfl,
    let m₁ := maj.majorizer (cast h' t₁) in 
    let m₂ := maj.majorizer (cast h' t₂) in 
    let m₁' := type.cast (maj_type.𝕄_app σ 𝕆) m₁ in
    let m₂' := type.cast (maj_type.𝕄_app σ 𝕆) m₂ in
    let m₁'' : ∥𝕄 σ∥ → ℕ := λ x', type.cast maj_type.𝕄_𝕆 (type.cast (maj_type.𝕄_app σ 𝕆) m₁ x') in 
    let m₂'' : ∥𝕄 σ∥ → ℕ := λ x', type.cast maj_type.𝕄_𝕆 (type.cast (maj_type.𝕄_app σ 𝕆) m₂ x') in
    let Φ : ∥𝕄 σ∥ → ℕ := λ x', (max (m₁'' x') (m₂'' x')) in 
    ⟨Φ, begin 
      intros x x' xmaj hA,
      use t₂ x,
      split, {
        have t₂_le_m₂ := maj.majorizes_le (maj.majorizes_app x x' (cast h' t₂) m₂ xmaj (by simp only [cast_eq]; apply maj.majorizer_majorizes)),
        -- have : (cast h' t₂) x = t₂ x := by simp,
        -- rw this at t₂_le_m₂, clear this,
        have : m₂'' x' ≤ Φ x' := by { dsimp only [Φ], exact le_max_right _ _, },
        exact le_trans t₂_le_m₂ this, 
      }, { 
        dsimp' at h,
        simp_rw [trivialA, trivialB] at h,
        specialize h (y x),
        dsimp at h,
        have : ((t x).snd (λ (_x : ℕ), 𝕎_inh')).fst = t₂ x := by refl,
        rw this at h,
        apply h,
        apply hA,
        have : ((t x).fst (λ (_x : ℕ), 𝕎_inh') (λ (_x : ℕ) (_x_1 : (B _x x).mwc.fst), ℂ_inh')).fst = t₁ x, refl,
        rw this, clear this,
        have t₁_le_m₁ := maj.majorizes_le (maj.majorizes_app x x' (cast h' t₁) m₁ xmaj (by simp only [cast_eq]; apply maj.majorizer_majorizes)),
        -- have : (cast h' t₁) x = t₁ x := by simp,
        -- rw this at t₁_le_m₁, clear this,
        have : m₁'' x' ≤ Φ x' := by { dsimp only [Φ], exact le_max_left _ _, },
        exact le_trans t₁_le_m₁ this,
      }
    end⟩

end

#print axioms metatheorem
  -- open formula (𝕎_inh' ℂ_inh')
  -- set_option pp.proofs true
  -- def metatheorem (𝕄 : 𝕋 → 𝕋) [maj_type 𝕄] (maj : majorizability 𝕄) (admissible : admissible_greq @greq) {σ : 𝕋} (A B : ∥𝕆 // gri∥ → ∥σ∥ → 𝔽) (Γ : premises') (premise_realizer : Π {γ : 𝔽}, γ ∈ Γ → dia.realizer γ)
  -- -- (trivialA : ∀ x u, (A x u).dia 𝕎_inh' ℂ_inh' ↔ ∥A x u∥) (trivialB : ∀ x v, (B x v).dia 𝕎_inh' ℂ_inh' ↔ ∥B x v∥)
  -- (prf : proof @greq {with_markov := tt, with_ip := tt} Γ (∀∀ x : ∥σ∥, ((∀∀ u : ∥𝕆∥, A u x) ⟹ (∃∃ v : ∥𝕆∥, B v x)))) 
  -- : {φ : ∥𝕄 σ∥ → ∥𝕆 // gri∥ // ∀ (x : ∥σ∥) (x' : ∥𝕄 σ∥) (_ : maj.majorizes x x'), (∀ u : ℕ, u ≤ φ x' → ∥A u x∥) → (∃ v : ℕ, v ≤ φ x' ∧ ∥B v x∥)} :=
  -- let ⟨t, h⟩ := prf.dia_realize admissible @premise_realizer in 
  -- by {
  --   dsimp' at t,
  --   dsimp' at h,
  --   type_check t,
  --   have trivialA : ∀ a b x y, (A a b).dia x y ↔ ∥A a b∥ := sorry,
  --   have trivialB : ∀ a b x y, (B a b).dia x y ↔ ∥B a b∥ := sorry,
  --   simp_rw [trivialA, trivialB] at h,
  --   -- set t' := λ y : (Σ (x : ∥σ∥), (Π (x_1 : ℕ), (A x_1 x).mwc.fst) × Π (x_1 : ℕ), (B x_1 x).mwc.fst → (B x_1 x).mwc.snd), t y.fst with ht',
  --   set y' : ∥σ∥ → (Σ (x : ∥σ∥), (Π (x_1 : ℕ), (A x_1 x).mwc.fst) × Π (x_1 : ℕ), (B x_1 x).mwc.fst → (B x_1 x).mwc.snd) 
  --     := λ x, sigma.mk x ⟨(λ _, 𝕎_inh'), (λ _ _, ℂ_inh')⟩,
  --   set t₁ := λ x, (t x).1,
  --   set t₂ := λ x, (t x).2,
  --   let t₁' : ∥σ∥ → ℕ := λ x, (t₁ x (y' x).2.1 (y' x).2.2).1,
  --   let t₂' : ∥σ∥ → ℕ := λ x, (t₂ x (y' x).2.1).1,
  --   let t₁'' : ∥σ∥ → ℕ := λ x, (t₁ x (λ _, 𝕎_inh') (λ _ _, ℂ_inh')).1,
  --   let t₂'' : ∥σ∥ → ℕ := λ x, (t₂ x (λ _, 𝕎_inh')).1,
  --   have : (∥σ∥ → ℕ) = ∥σ ↣ 𝕆∥ := sorry,
  --   let m₁ := (maj.majorizer (cast this t₁'')),
  --   let m₂ := (maj.majorizer (cast this t₂'')),
  --   set m₁' := type.cast (maj_type.𝕄_app σ 𝕆) m₁ with eq_m₁',
  --   set m₂' := type.cast (maj_type.𝕄_app σ 𝕆) m₂ with eq_m₂', 
  --   ss at m₁',
  --   ss at m₂',
  --   let Φ : ∥𝕄 σ∥ → ℕ := λ x', type.cast maj_type.𝕄_𝕆 (max (m₁' x') (m₂' x')),
    
  --   refine subtype.mk Φ _,
  --   intros x x' xmaj h',
  --   use t₂'' x,
  --   split,
  --   have := maj.majorizes_app x x' (cast this t₂'') m₂ xmaj sorry,
  --   have := maj.majorizes_le this,
  --   dsimp at this,
  --   rw ←eq_m₂' at this_1,
  -- }