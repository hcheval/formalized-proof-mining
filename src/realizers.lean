import proof


section realizers 

  variables {ι : Type}  {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq

  namespace dia 


  section logical_axioms 

    open formula

    variables {σ τ : 𝕋}
    variables (A B C : 𝔽) (P : ∥σ∥ → 𝔽)
    variables (Γ : premises ι gri)

    def and_contr : realizer (A ⟹ A ⋀ A) :=
      subtype.mk
        (⟨(λ x y, if A.dia x y.fst then y.2 else y.1), (λ x, (x, x))⟩)
        (begin
          rintros ⟨y₁, ⟨y₂₁, y₂₂⟩⟩ h,
          simp only [dia, dite_eq_ite, id.def] at *,
          by_cases h' : A.dia y₁ y₂₁,
          {
            simp only [*, if_true] at h,
            exact ⟨h', h⟩,
          },
          {
            simp only [*, if_false] at h,
            contradiction,
          },
        end)
    
    def or_contr : realizer (A ⋁ A ⟹ A) :=
      subtype.mk
      ((λ x y, (y, y)), (λ x, match x with | (sum.inl x') := x' | (sum.inr x') := x' end)) 
      (begin 
        rintros ⟨y₁, y₂⟩ h,
        cases y₁;
        assumption,
      end)

    def and_weak : realizer (A ⋀ B ⟹ A) := 
      subtype.mk 
      (prod.mk (λ ⟨y1, y2⟩ y3, (y3, ℂ_inh B)) (λ ⟨y1, y2⟩, y1))
      (begin 
        rintros ⟨⟨y₁₁, y₁₂⟩ , y₂⟩ ⟨h₁, h₂⟩,
        assumption,
      end)

    def or_weak : realizer (A ⟹ A ⋁ B) :=
      subtype.mk 
      ((λ x y, y.fst), (λ x, sum.inl x))
      (begin 
        intros y h,
        assumption,
      end)

    def exfalso : realizer (prime false ⟹ A) :=
      subtype.mk 
      ⟨(λ _ _, punit.star), (λ _, 𝕎_inh A)⟩
      (begin 
        intros y h,
        cases h,
      end)

    def and_perm : realizer (A ⋀ B ⟹ B ⋀ A) :=
      subtype.mk 
      (((λ x y, (y.2, y.1)), λ x, (x.2, x.1)))
      (begin 
        rintros ⟨⟨y₁₁, y₁₂⟩, ⟨y₂₁, y₂₂⟩⟩ h,
        dsimp only [dia] at *,
        exact and.comm.mp h,
      end)

    def or_perm : realizer (A ⋁ B ⟹ B ⋁ A) :=
      subtype.mk 
      (((λ x y, y.swap), (λ x, x.swap)))
      (begin 
        rintros ⟨y₁, ⟨y₂₁, y₂₂⟩⟩ h, 
        cases y₁;
        assumption,
      end)
    
    def univ_ax : Π a : ∥σ∥, realizer (universal' σ P ⟹ P a) :=
      λ a, 
      subtype.mk 
      (((λ x y, ⟨_, y⟩), (λ x, x a))) 
      (begin 
        intros y h,
        exact h,
      end)

    def exist_ax : Π a : ∥σ∥, realizer (P a ⟹ existential' σ P) :=
      λ a,
      subtype.mk
      (((λ x y, y a x), (λ x, ⟨a, x⟩)))
      (begin 
        intros y h,
        exact h,
      end)

  end logical_axioms


  section logical_rules 

    open formula 

    local attribute [simp] dia

    variables {Γ : premises ι gri}
    variables {σ τ : 𝕋} 
    variables {A B C : 𝔽} {P : ∥σ∥ → 𝔽}

    def of_prime_true {p : Prop} [decp : decidable p] (hp : p) : realizer (@prime _ gri p decp) := 
      subtype.mk 
      unit.star 
      (λ _, hp)

    def mp : realizer A → realizer (A ⟹ B) → realizer B :=
      λ hA hAB, subtype.mk 
      ((hAB).1.2 (hA).1)
      (begin 
        intros y,
        let h₁ := (hA).2,
        let h₂ := (hAB).2, 
        dsimp only [dia, ℂ, mwc, dia, 𝕎] at h₂,
        simp only [prod.forall, subtype.val_eq_coe] at h₂,
        apply h₂,
        apply h₁,
      end)

    def syl : realizer (A ⟹ B) → realizer (B ⟹ C) → realizer (A ⟹ C) := 
      λ hAB hBC, subtype.mk 
      ((λ x y, (hAB).1.1 x ((hBC).1.1 ((hAB).1.2 x) y)), (λ x, (hBC).1.2 ((hAB).1.2 x)))
      (begin 
        intros y h,
        let h₁ := (hAB).2,
        let h₂ := (hBC).2,
        dsimp only [ℂ, mwc, dia, 𝕎] at h₁ h₂,
        simp only [prod.forall, subtype.val_eq_coe] at h₁ h₂,
        apply h₂,
        apply h₁,
        apply h,
      end)

    def exportation : realizer (A ⋀ B ⟹ C) → realizer (A ⟹ (B ⟹ C)) :=
      λ h, subtype.mk
      (((λ x y, ((h).1.1 (x, y.1) y.2).1), (λ x, ((λ y z, ((h).1.1 (x, y) z).2), (λ y, (h).1.2 (x, y)))))) 
      (begin
        rintros ⟨y₁, ⟨y₂₁, y₂₂⟩⟩,
        let h' := (h).2,
        intros h₁ h₂,
        dsimp only [formula.ℂ, formula.𝕎, formula.dia, formula.mwc] at *,
        simp only [prod.forall] at *,
        exact h' _ _ _ ⟨h₁, h₂⟩,
      end)

    def importation : realizer (A ⟹ (B ⟹ C)) → realizer (A ⋀ B ⟹ C) := 
      λ h, subtype.mk 
      (((λ x y, ((h).1.1 x.1 (x.2, y), ((h).1.2 x.1).1 x.2 y)), (λ x, ((h).1.2 x.1).2 x.2)))
      (begin 
        rintros ⟨⟨y₁₁, y₁₂⟩, y₂⟩,
        let h' := (h).2,
        rintros h₁,
        dsimp only [ℂ, mwc, dia, 𝕎] at h' h₁ ⊢,
        simp only [prod.forall, subtype.val_eq_coe] at h' h₁ ⊢,
        specialize h' y₁₁ ⟨y₁₂, y₂⟩,
        apply h',
        { apply h₁.1, },
        { apply h₁.2, },
      end)

    def univ_rule : (Π x : ∥σ∥, realizer (A ⟹ P x)) → realizer (A ⟹ universal' σ P) :=
      λ h, subtype.mk 
      ((λ x y, (h y.1).1.1 x y.2), (λ x y, (h y).1.2 x))
      (begin 
        rintros ⟨y1, ⟨z, y2⟩⟩,
        let ht := (h z).property,
        specialize ht ⟨y1, y2⟩,
        exact ht,
      end)

    def exist_rule : (Π x : ∥σ∥, realizer (P x ⟹ A)) → realizer (existential' σ P ⟹ A) :=
      λ h, subtype.mk 
      (((λ x y z v, (h z).1.1 v y), (λ x, (h x.1).1.2 x.2)))
      (begin 
        rintros ⟨⟨y1, y2⟩, y3⟩,
        let ht := (h y1).property,
        specialize ht ⟨y2, y3⟩,
        exact ht,  
      end)

    
    def expansion : realizer (A ⟹ B) → realizer ((C ⋁ A) ⟹ (C ⋁ B)) :=
      λ h, subtype.mk 
        (prod.mk
          (λ x y, 
            match x with 
            | (sum.inl x') := (y.1, ((h).1.1 (𝕎_inh _) y.2))
            | (sum.inr x') := (y.1, (h).1.1 x' y.2)
            end
          )
          (λ x, 
            match x with 
            | (sum.inl x') := sum.inl x'
            | (sum.inr x') := sum.inr ((h).1.2 x')
            end
          )
        )
        (begin
          rintros ⟨y₁, ⟨y₂₁, y₂₂⟩⟩,
          let h' := (h).property,
          dsimp only [ℂ, mwc, dia, 𝕎] at *,
          intros hA,
          cases y₁,
          case sum.inl 
          { assumption, },
          case sum.inr 
          { dsimp only [mwc, realizer, dia] at *, 
            simp only [prod.forall, subtype.val_eq_coe] at *, 
            solve_by_elim, },
        end)
        
      
    def qfer (admissible : admissible_greq @greq) (a b : ∥σ∥) : realizer (a ≅ b) → realizer (P a ⟹ P b) :=
      λ h, subtype.mk 
      ( have eqab : a = b := eq_of_eqext_realizer admissible _ _ h, 
        have eqℂ : (P a).ℂ = (P b).ℂ := congr_arg ℂ (congr_arg P eqab),
        have eq𝕎 : (P a).𝕎 = (P b).𝕎 := congr_arg 𝕎 (congr_arg P eqab),
        prod.mk 
          (λ u v, cast (eq.symm eqℂ) v) 
          (λ u, cast eq𝕎 u))
      (begin 
        intros y h',
        have eqab : a = b := eq_of_eqext_realizer admissible _ _ h,
        subst eqab,
        exact h',
      end)

  end logical_rules

  section induction_rule 

    open formula

    def ir {A : ∥𝕆 // gri∥ → 𝔽} (m : ∥𝕆 // gri∥) :
       realizer (A nat.zero) → (Π n : ∥𝕆 // gri∥, realizer (A n ⟹ A n.succ)) → realizer (A m) :=
    λ h0 hi, subtype.mk 
      (nat.rec_on m h0.val (λ n p, (hi n).val.snd p)) 
      (begin
        intros y,
        induction m,
        case zero {
          exact h0.2 y,
        },
        case succ: m ih{
          have := λ n, (hi n).property,
          dsimp only [ℂ, mwc, 𝕎] at this,
          simp only [dia] at this,
          simp only,
          set u : (A m).𝕎 := nat.rec h0.val (λ (n : ℕ), (hi n).val.snd) m,
          specialize this m,
          specialize this ⟨u, y⟩,
          apply this,
          apply ih,
        }
      end)

  end induction_rule

  section other 

    open formula 
    
    def markov {σ : 𝕋} (A : ∥σ∥ → 𝔽) 
      [uw : ∀ x : ∥σ∥, subsingleton (A x).𝕎]
      [uc : ∀ x : ∥σ∥, subsingleton (A x).ℂ] :
      realizer (∼(∀∀ (x : ∥σ∥) , ∼(A x)) ⟹ (∃∃ (x : ∥σ∥) , A x)) :=
      subtype.mk 
        (prod.mk (λ _ _, ℂ_inh _) (λ h, ⟨(h.1 (𝕎_inh _) (ℂ_inh _)).1, 𝕎_inh _⟩)) 
        (begin
          dsimp only [negation, ℂ, mwc, dia] at *,
          simp only [ℂ, prod.forall, 𝕎] at *,
          intros y u v h,
          set φ := (((y, u), v).fst.fst (∀∀ (x : ∥σ∥), A x⟹(falsum ι gri)).𝕎_inh (falsum ι gri).ℂ_inh).fst,
          set ψ₁ := ((∀∀ (x : ∥σ∥), A x⟹(falsum ι gri))⟹(falsum ι gri)).ℂ_inh.fst with eq_ψ₁,
          rw ←eq_ψ₁ at *,
          set ψ₂ := ((∀∀ (x : ∥σ∥), A x⟹(falsum ι gri))⟹(falsum ι gri)).ℂ_inh.snd with eq_ψ₂,
          rw ←eq_ψ₂ at *,
          set χ := ((y, u), v) with eq_χ,
          rw ←eq_χ at *,
          dsimp only at h,
          have : φ = (y ψ₁ ψ₂).fst := rfl,
          rw this, clear this,
          rw [imp_false, imp_false, dia_not_not] at h,
          have : (χ.fst.fst ψ₁ ψ₂).snd.fst = (A (χ.fst.fst ψ₁ ψ₂).fst).𝕎_inh := 
            subsingleton_iff.mp (uw (χ.fst.fst ψ₁ ψ₂).fst) _ _,
          rw ←this, clear this,
          have : 
            (ψ₁ (χ.fst.fst ψ₁ ψ₂).fst).fst (χ.fst.fst ψ₁ ψ₂).snd.fst (χ.fst.fst ψ₁ ψ₂).snd.snd 
            = 
            v (χ.fst.fst ψ₁ ψ₂).fst (χ.fst.fst ψ₁ ψ₂).snd.fst :=
            subsingleton_iff.mp (uc (χ.fst.fst ψ₁ ψ₂).fst) _ _,
          rw ←this, clear this,
          apply h,
        end)

    def ip {σ τ : 𝕋} (A : ∥σ∥ → 𝔽) (B : ∥τ∥ → 𝔽)
      [uwA : ∀ x : ∥σ∥, subsingleton (A x).𝕎] 
      [ucB : ∀ y : ∥τ∥, subsingleton (B y).ℂ] :
      realizer $ ((∀∀ (x : ∥σ∥) , A x) ⟹ (∃∃ (y : ∥τ∥) , B y)) ⟹ ∃∃ (y : ∥τ∥) , ((∀∀ (x : ∥σ∥) , A x) ⟹ B y) :=
      subtype.mk 
        (let f := λ x : ∥σ∥, 𝕎_inh (A x) in 
        let g := λ (y : ∥τ∥) (w : 𝕎 (B y)), ℂ_inh (B y) in 
        prod.mk
          (λ x y, (f, g))
          (λ a, ⟨(a.2 f).1, ((λ z _, a.1 f g), (λ z, (a.2 f).2))⟩)
        )
        (begin 
          dsimp only [ℂ, mwc, dia, 𝕎] at *,
          simp only [ℂ, prod.forall, 𝕎] at *,
          intros x y u h₁,
          unfreezingI { dsimp only at *},
          set a := x (λ (x : σ.interpret), (A x).𝕎_inh) (λ (y : τ.interpret) (w : (B y).mwc.fst), (B y).ℂ_inh) with eq_a,
          rw ←eq_a at *,
          set b := y (λ (x : σ.interpret), (A x).𝕎_inh) with eq_b,
          rw ←eq_b at *,
          set c := λ (z : Π (x : σ.interpret), (A x).mwc.fst), b.snd with eq_c,
          rw ←eq_c at *,
          intros h₂,
          have : (u b.fst (λ (z : Π (x : σ.interpret), (A x).mwc.fst) (ᾰ : (B b.fst).mwc.snd), a, c)).snd = ℂ_inh (B b.fst) := 
            subsingleton_iff.mp (ucB b.fst) _ _,
          rw this, clear this,
          have : (u b.fst (λ (z : Π (x : σ.interpret), (A x).mwc.fst) (ᾰ : (B b.fst).mwc.snd), a, c)).fst a.fst = 𝕎_inh (A a.fst) 
            := subsingleton_iff.mp (uwA a.fst) _ _,
          rw this at h₂, clear this,
          apply h₁,
          exact h₂,
        end)

    def qfac {σ τ : 𝕋} (A : ∥σ∥ → ∥τ∥ → 𝔽) 
      [uw : ∀ x y, subsingleton (A x y).𝕎] [uc : ∀ x y, subsingleton (A x y).ℂ] :
      realizer $ (∀∀ x : ∥σ∥, ∃∃ y : ∥τ∥, A x y ⟹ ∃∃ Y : ∥σ ↣ τ∥, ∀∀ x : ∥σ∥, A x (Y x)) :=
    subtype.mk 
      (by {
        dsimp at *,
        intros a,
        sorry,
      }
      ) 
      (begin 
        dsimp at *,
        intros,
      end)


  end other

  end dia 
  
end realizers


section soundness 

  namespace proof 

  variables {ι : Type}  {gri : ground_interpretation ι}
  local notation `𝔽` := formula ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri∥ → ∥𝕏 i // gri∥ → 𝔽}
  variables (admissible : admissible_greq @greq)

  include admissible

  def dia_realize {Γ : premises ι gri} (premise_realizer : (Π {γ : 𝔽}, γ ∈ Γ → dia.realizer γ)) : 
  Π {A : 𝔽}, proof @greq {with_markov := tt, with_ip := tt} Γ A → dia.realizer A
  | A (@premise _ _ _ _ _ .(A) hmem) := premise_realizer hmem
  | _ (@of_prime_true _ _ _ _ _ p decp h) := @dia.of_prime_true _ _ p decp h
  | _ (and_contr _) := dia.and_contr _ 
  | _ (or_contr _) := dia.or_contr _ 
  | _ (and_weak _ _) := dia.and_weak _ _
  | _ (or_weak _ _) := dia.or_weak _ _ 
  | _ (and_perm _ _) := dia.and_perm _ _ 
  | _ (or_perm _ _) := dia.or_perm _ _ 
  | _ (univ_ax _ _) := dia.univ_ax _ _ 
  | _ (exist_ax _ _) := dia.exist_ax _ _ 
  | _ (exfalso _) := dia.exfalso _ 
  | _ (mp prfA prfAB) := dia.mp prfA.dia_realize prfAB.dia_realize
  | _ (syl prfAB prfBC) := dia.syl prfAB.dia_realize prfBC.dia_realize
  | _ (importation prf) := dia.importation prf.dia_realize
  | _ (exportation prf) := dia.exportation prf.dia_realize
  | _ (expansion prf) := dia.expansion prf.dia_realize
  | _ (univ_rule prf) := dia.univ_rule $ λ x, (prf x).dia_realize
  | _ (exist_rule prf) := dia.exist_rule $ λ x, (prf x).dia_realize
  | _ (ir m prf_0 prf_succ) := dia.ir m prf_0.dia_realize $ λ n, (prf_succ n).dia_realize
  | _ (qfer σ x y A prf) := dia.qfer admissible x y prf.dia_realize
  | _ (@markov _ _ _ _ _ σ A uw uc _) := @dia.markov _ _ _ A uw uc
  | _ (@ip _ _ _ _ _ _ _ A B uwA ucB _) := @dia.ip _ _ _ _ A B uwA ucB

  end proof
end soundness