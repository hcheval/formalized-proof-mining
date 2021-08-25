import tactic
import formula 
import utils


section witness_counter 

  variables {ι : Type}  {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq

  namespace formula  

  @[simp]
  def mwc : 𝔽 → Type × Type 
  -- does not allow simply `prime p` (probably a bug in the equation compiler)
  | (@prime _ _ p _) := (unit, unit)
  | (A ⋀ B) := (A.mwc.1 × B.mwc.1, A.mwc.2 × B.mwc.2)
  | (A ⋁ B) := (A.mwc.1 ⊕ B.mwc.1, A.mwc.2 × B.mwc.2)
  | (A ⟹ B) := ((A.mwc.1 → B.mwc.2 → A.mwc.2) × ((A.mwc.1 → B.mwc.1)), A.mwc.1 × B.mwc.2)
  | (universal' σ A) := ((Π x : ∥σ∥, (A x).mwc.1), (Σ x : ∥σ∥, (A x).mwc.2))
  | (existential' σ A) := ((Σ x : ∥σ∥, (A x).mwc.1), (Π x : ∥σ∥, (A x).mwc.1 → (A x).mwc.2))

  @[reducible, simp, pp_nodot] 
  def 𝕎 (A : 𝔽) : Type := A.mwc.1
  @[reducible, simp, pp_nodot]
  def ℂ (A : 𝔽) : Type := A.mwc.2 
  

  -- mutual def 𝕎, ℂ 
  -- with 𝕎 : 𝔽 → Type 
  -- | (prime p) := unit
  -- | (A ⋀ B) := 𝕎 A × 𝕎 B
  -- | (A ⋁ B) := 𝕎 A ⊕ 𝕎 B
  -- | (A ⟹ B) := (𝕎 A → ℂ B → ℂ A) × (𝕎 A → 𝕎 B)
  -- | (universal' σ A) := Π x : ∥σ∥, 𝕎 (A x) 
  -- | (existential' σ A) := Σ x : ∥σ∥, 𝕎 (A x) 
  -- with ℂ : 𝔽 → Type
  -- | (prime p) := unit
  -- | (A ⋀ B) := ℂ A × ℂ B
  -- | (A ⋁ B) := ℂ A × ℂ B 
  -- | (A ⟹ B) := 𝕎 A × ℂ B 
  -- | (universal' σ A) := Σ x : ∥σ∥, 𝕎 (A x) → ℂ (A x)
  -- | (existential' σ A) := Π x : ∥σ∥, 𝕎 (A x) → ℂ (A x)



  def mwc_inh : Π A : 𝔽, A.𝕎 × A.ℂ 
  | (@prime _ _ p _) := (unit.star, unit.star)
  | (A ⋀ B) := ((A.mwc_inh.1, B.mwc_inh.1), (A.mwc_inh.2, B.mwc_inh.2))
  | (A ⋁ B) := (sum.inl A.mwc_inh.1, (A.mwc_inh.2, B.mwc_inh.2)) --ugly noncanonicity
  | (A ⟹ B) := (((λ _ _, A.mwc_inh.2), (λ _, B.mwc_inh.1)), (A.mwc_inh.1, B.mwc_inh.2))
  | (universal' σ A) := ((λ x, (A x).mwc_inh.1), ⟨σ.inh, (A σ.inh).mwc_inh.2⟩)
  | (existential' σ A) := (⟨σ.inh, (A σ.inh).mwc_inh.1⟩, (λ x _, (A x).mwc_inh.2))

  def 𝕎_inh (A : 𝔽) : A.𝕎 := A.mwc_inh.1
  def ℂ_inh (A : 𝔽) : A.ℂ := A.mwc_inh.2

  def 𝕎_inh' {A : 𝔽} := 𝕎_inh A
  def ℂ_inh' {A : 𝔽} := ℂ_inh A

  end formula

end witness_counter

section dialectica 

  variables {ι : Type}  {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq

  namespace formula 

  @[simp]
  def dia : Π (A : 𝔽), A.𝕎 → A.ℂ → Prop
  | (@prime _ _ p _) x y := p 
  | (A ⋀ B) x y := (A.dia x.1 y.1) ∧ (B.dia x.2 y.2)
  | (A ⋁ B) x y := 
    match x with 
    | sum.inl xA := A.dia xA y.1
    | sum.inr xB := B.dia xB y.2
    end
  | (A ⟹ B) x y := (A.dia y.1 (x.1 y.1 y.2)) → (B.dia (x.2 y.1) y.2)
  | (universal A) x y := (A y.1).dia (x y.1) y.2
  | (existential A) x y := (A x.1).dia x.2 (y x.1 x.2)

  @[reducible, simp]
  def Dia (A : 𝔽) := ∃ x : 𝕎 A, ∀ y : ℂ A, A.dia x y

  --# TODO: better name
  inductive is_gamma2 : 𝔽 → Prop 
  | of_prime (p : Prop) [decidable p] : is_gamma2 (prime p)
  | of_conjunction (A B : 𝔽) : is_gamma2 A → is_gamma2 B → is_gamma2 (A ⋀ B)
  | of_disjunction (A B : 𝔽) : is_gamma2 A → is_gamma2 B → is_gamma2 (A ⋁ B)
  | of_universal {σ : 𝕋} (A : ∥σ∥ → 𝔽) : (∀ x : ∥σ∥, is_gamma2 (A x)) → is_gamma2 (universal A)

  @[reducible, simp]
  def is_gamma2_like (A : 𝔽) : Prop := A.Dia → ∥A∥

  @[simp]
  lemma dia_disj_left (A B : 𝔽) (x : A.𝕎) (y : (A ⋁ B).ℂ) : (A ⋁ B).dia (sum.inl x) y ↔ A.dia x y.1 := 
    by simp 

  @[simp]
  lemma dia_disj_right (A B : 𝔽) (x : B.𝕎) (y : (A ⋁ B).ℂ) : (A ⋁ B).dia (sum.inr x) y ↔ B.dia x y.2 := 
    by simp 

  end formula 

  @[simp]
  def dia.realizer (A : 𝔽) := {t : A.𝕎 // ∀ y : A.ℂ, A.dia t y}


  instance dia.decidable (A : 𝔽) (x : A.𝕎) (y : A.ℂ) : decidable (A.dia x y) := 
  begin 
    induction A,
    case prime 
    { assumption, },
    case conjunction: A B ihA ihB 
    {
      simp only [formula.dia],
      specialize ihA x.fst y.fst,
      specialize ihB x.snd y.snd,
      exact @and.decidable _ _ ihA ihB,
    },
    case disjunction: A B ihA ihB {
      simp only [formula.dia],
      dsimp only [formula.mwc, formula.𝕎] at x,
      cases x,
      case sum.inl 
      { exact ihA x y.fst, },
      { exact ihB x y.snd, },
    },
    case implication: A B ihA ihB {
      simp only [formula.dia],
      specialize ihA y.fst (x.fst y.fst y.snd),
      specialize ihB (x.snd y.fst) y.snd,
      refine @implies.decidable _ _ ihA ihB,
    },
    case universal: σ A ihA {
      simp only [formula.dia],
      dsimp at x y,
      exact ihA y.fst (x y.fst) y.snd,
    },
    case existential: σ A ihA {
      simp only [formula.dia],
      dsimp at x y,
      exact ihA x.fst x.snd (y x.fst x.snd),
    }
  end

  

  lemma dia_not_not (A : 𝔽) (x : A.𝕎) (y : A.ℂ) : ¬¬(A.dia x y) ↔ A.dia x y := 
    iff.intro 
    (λ h, if h' : A.dia x y then h' else false.elim (h h')) 
    (λ h h', h' h)


  def Dia_of_realizer {A : 𝔽} : dia.realizer A → A.Dia :=
    λ r, ⟨r.val, r.property⟩


  lemma interpretation_of_gamma2_Dia {A : 𝔽} (gA : A.is_gamma2) : A.Dia → ∥A∥ :=
  begin 
    induction gA; intros h,
    case of_prime: p decp {
      dsimp at *,
      simp at *,
      exact h,
    },
    case of_conjunction: B C gB gC ihB ihC {
      dsimp at *, simp at *,
      rcases h with ⟨w, ⟨w', h⟩⟩,
      refine ⟨ihB w (λ y, (h y formula.ℂ_inh').1), ihC w' (λ y, (h formula.ℂ_inh' y).2)⟩,
    },
    case of_disjunction: B C gB gC ihB ihC {
      dsimp at *, simp at *,
      cases h,
      {
        rcases h with ⟨w, h⟩,
        refine or.inl (ihB w (λ y, h y formula.ℂ_inh')),
      },
      {
        rcases h with ⟨w, h⟩,
        refine or.inr (ihC w (λ y, h formula.ℂ_inh' y)),
      }
    },
    case of_universal: σ B gB ihB {
      dsimp at *, simp at *,
      intros a,
      rcases h with ⟨w, h⟩,
      specialize h a,
      dsimp only at h,
      exact ihB a (w a) h,
    }
  end

  example (A : 𝔽) : ∥A∥ → A.Dia :=
  begin 
    induction A; intros h,
    case prime: p decp {
      dsimp at *, simp at *, 
      exact h,
    },
    case conjunction: B C ihB ihC {
      dsimp at *, simp at *,
      specialize ihB h.1,
      specialize ihC h.2,
      rcases ihB with ⟨wB, hB⟩,
      rcases ihC with ⟨wC, hC⟩,
      use wB, use wC,
      tidy?,
    },
    case disjunction: B C ihB ihC {
      dsimp at *, simp at *,
      cases h,
      {
        specialize ihB h,
        rcases ihB with ⟨wB, hB⟩,
        left,
        use wB,
        tidy?,
      },
      {
        specialize ihC h,
        rcases ihC with ⟨wC, hC⟩,
        right,
        use wC,
        tidy?,
      }
    },
    case universal: σ B ihB {
      dsimp at *, simp at *,
      specialize ihB h,
    }
  end


end dialectica 



section kinds_of_formulas 
 
  variables {ι : Type} {gri : ground_interpretation ι} 
  local notation `𝔽` := formula ι gri
  local notation `𝕋` := type ι gri
  variables {greq : Π {i : ι}, ∥𝕏 i // gri ∥ → ∥𝕏 i // gri ∥ → 𝔽}
  local infixr `≅` : 35 := formula.eqext @greq


  section 

    @[class, reducible] 
    def dia_trivial (A : 𝔽) := unique A.𝕎 × unique A.ℂ

    variables {A B : 𝔽} [inst : dia_trivial A] [dia_trivial B]

    instance : unique A.𝕎 := inst.1
    instance : unique A.ℂ := inst.2

    local attribute [reducible] formula.mwc formula.𝕎 formula.ℂ

    instance dia_trivial_prime {p : Prop} [decp : decidable p] : dia_trivial (formula.prime p : 𝔽) := 
    ⟨infer_instance, infer_instance⟩

    instance dia_trivial_conjunction {A B : 𝔽} [dia_trivial A] [dia_trivial B] : dia_trivial (A ⋀ B) := 
    ⟨infer_instance, infer_instance⟩

    instance dia_trivial_implication {A B : 𝔽} [dia_trivial A] [dia_trivial B] : dia_trivial (A ⟹ B) :=
    ⟨infer_instance, infer_instance⟩

    -- immediate
    instance dia_trivial_of_qf_disj_free {A : 𝔽} (qfA : A.is_qf_disj_free) : dia_trivial A :=
    sorry 

  end

  section 
  
    def Dia_iff_interp (A : 𝔽) : Prop := A.Dia ↔ ∥A∥

    lemma Dia_iff_interp_of_dia_trivial (A : 𝔽) [dia_trivial A] : Dia_iff_interp A := 
    begin 
      split; intros h,
      {
        ss [formula.Dia] at h,
      }
    end

  end 

  /-
  todo: 
    there is a class of formulas for which A.Dia ↔ ∥A∥
    there is a class of formulas for which unique A.𝕎 and A.ℂ 

  -/


  example (A : 𝔽) : A.is_qf_disj_free → subsingleton A.𝕎 :=
  begin 
    sorry, --easy
  end

  @[instance]
  lemma trivial_witness_of_purely_univ_disj_free (A : 𝔽) : A.purely_univ_disj_free → subsingleton A.𝕎 :=
  begin 
    intros h,
    induction h,
    case of_qf_disj_free: B qfB {
      sorry, --easy
    },
    case of_univ: σ B qfB ih {
      simp only [formula.𝕎, formula.mwc], 
      by_ext a b x,
      specialize ih x,
      exact subsingleton_iff.mp ih (a x) (b x),
    }
  end


  lemma dia_iff_interpretation_of_purely_univ_disj_free (A : 𝔽) : A.purely_univ_disj_free → ((∃ x, ∀ y, A.dia x y) ↔ ∥A∥) :=
  begin 
    intros h,
    induction h,
    case of_univ: σ B univ ih {
      split,
      {
        intros a x,
        specialize ih x,
        rw ←ih,
        tidy?,
      },
      {
        intros hB,
        have : subsingleton (Π x : ∥σ∥, (B x).𝕎) :=
        begin 
          by_ext a b x,
          have : subsingleton (B x).𝕎 := sorry,
          exact subsingleton_iff.mp this (a x) (b x),
        end,
        dsimp only [formula.ℂ, formula.𝕎, formula.dia],
        set w := λ x, (B x).𝕎_inh,
        use w,
        intros y,
        specialize ih y.1,
        rcases ih with ⟨ihl, ihr⟩,
        dsimp at hB,
        specialize hB y.1,
        specialize ihr hB,
        rcases ihr with ⟨w', ihr⟩,
        specialize ihr y.2,
        have : w' = w y.1 := 
        begin 
          -- apply @subsingleton.elim _ (this _),
          sorry, 
          -- ??? question: is it the case that 
          -- subsingleton (Π x : α, β x) → ∀ x : α, subsingleton (β x) ???
        end
      }
    }


    -- induction A,
    -- case universal: σ B ih {
    --   dsimp only at ih,
    --   dsimp [formula.mwc, formula.𝕎, formula.ℂ] at *,
    --   split,
    --   {
    --     intros a x,
    --     specialize ih x sorry,
    --     rw ←ih,
    --     tidy?,
    --   },
    --   {
    --     intros a,
    --     have : subsingleton (Π (x : σ.interpret), (B x).mwc.fst) :=
    --     begin 
    --       apply subsingleton.intro,
    --       intros a b,
    --       ext x,
    --       have : subsingleton (B x).𝕎 := sorry,
    --       exact subsingleton_iff.mp this (a x) (b x),
    --     end
    --   }
    -- }
  end

end kinds_of_formulas 



section eqext_in_relation_to_dialectica

  variables {ι : Type} {gri : ground_interpretation ι}
  local notation `𝕋` := type ι gri
  local notation `𝔽` := formula ι gri

  structure admissible_greq (gre : Π {i : ι}, ∥𝕏 i // gri∥ → ∥𝕏 i // gri∥ → 𝔽) :=
  (trivial_witness : ∀ (i : ι) (a b : ∥𝕏 i∥), subsingleton (gre a b).𝕎)
  (gamma2 : ∀ (i : ι) (a b : ∥𝕏 i∥), (gre a b).is_gamma2)
  (greq_iff_eq : ∀ (i : ι) (a b : ∥𝕏 i∥), ∥gre a b∥ ↔ a = b)

  variables {greq : Π {i : ι}, ∥𝕏 i // gri∥ → ∥𝕏 i // gri∥ → 𝔽}
  local infixl `≅` : 35 := formula.eqext @greq

  -- local attribute [simp] formula.dia formula.mwc formula.𝕎 formula.\bbC
  lemma trivial_witness_eqext {σ : 𝕋} (x y : ∥σ∥) (admissible : admissible_greq @greq) : subsingleton (x ≅ y).𝕎 := 
  begin 
    induction σ,
    case zero {
      exact punit.subsingleton,
    },
    case ground: i {
      apply admissible.trivial_witness,
    },
    case arrow: ρ τ ihρ ihτ{
      simp only [formula.mwc, formula.𝕎, formula.eqext] at *,
      dsimp only [type.interpret] at *,
      fsplit,
      intros a b,
      ext1 z,
      exact subsingleton_iff.mp (ihτ (x z) (y z)) (a z) (b z),
    },
    case times: ρ τ ihρ ihτ {
      simp only [formula.𝕎, formula.eqext, formula.mwc] at *,
      dsimp only [type.interpret] at *,
      rcases x with ⟨x₁, x₂⟩, 
      rcases y with ⟨y₁, y₂⟩,
      specialize ihρ x₁ y₁,
      specialize ihτ x₂ y₂,
      dsimp only at *, 
      fsplit, 
      rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩, 
      simp only [prod.mk.inj_iff] at *, 
      fsplit,
      { exact subsingleton_iff.mp ihρ a₁ b₁, },
      { exact subsingleton_iff.mp ihτ a₂ b₂, },
    } 
  end 

  lemma gamma2_eqext {σ : 𝕋} (x y : ∥σ∥) (admissible : admissible_greq @greq) : (x ≅ y).is_gamma2 :=
  begin 
    induction σ,
    case ground: i {
      exact admissible.gamma2 _ _ _,
    },
    all_goals { constructor, },
    all_goals { tidy?, },
  end

  lemma eqext_iff_eq {σ : 𝕋} (x y : ∥σ∥) (admissible : admissible_greq @greq) : ∥x ≅ y∥ ↔ x = y :=
  begin 
    split,
    {
      induction σ; intros h,
      case zero {
          simpa,
      },
      case ground: i {
        apply (admissible.greq_iff_eq _ _ _).1,
        simpa,
      },
      case arrow: τ ρ ihτ ihρ {
        ss at h,
        ext z,
        specialize h z,
        specialize ihρ (x z) (y z),
        exact ihρ h,
      },
      case times: τ ρ ihτ ihρ {
        simp only [formula.eqext, formula.interpret] at h,
        rcases h with ⟨h₁, h₂⟩,
        dsimp only [type.interpret] at *,
        rcases x with ⟨x₁, x₂⟩,
        rcases y with ⟨y₁, y₂⟩,
        simp only [prod.mk.inj_iff],
        simp only at h₁ h₂,
        split,
        { exact ihτ _ _ h₁, },
        { exact ihρ _ _ h₂, },
      },
    },
    {
      induction σ; intros h,
      case zero {
        simp *,
      },
      case ground: i {
        apply (admissible.greq_iff_eq _ _ _).2,
        exact h,
      },
      case arrow: τ ρ ihτ ihρ {
        subst h,
        dsimp,
        intros z,
        exact ihρ (x z) (x z) rfl,
      },
      case times: τ ρ ihτ ihρ {
        ss at *,
        dsimp' at *,
        cases x with x₁ x₂,
        cases y with y₁ y₂,
        cases h with h₁ h₂,
        ss at *,
        split,
        { exact ihτ _ _ rfl, },
        { exact ihρ _ _ rfl, },
      }
    }
  end 

  -- set_option trace.simplify.rewrite true
  -- lemma eqext_Dia_iff_eq {σ : 𝕋} (a b : ∥σ∥) (admissible : admissible_greq @greq) :
  --   (a ≅ b).Dia ↔ a = b :=
  -- begin 
  --   split,
  --   {
  --     induction σ,
  --     case zero { 
  --       intros h,
  --       dsimp only [formula.eqext, type.interpret, formula.Dia, formula.mwc, formula.𝕎, formula.ℂ, formula.dia] at h,
  --       simp only [forall_const, exists_const] at h,
  --       exact h,
  --     },
  --     case ground: i {
  --       intros h,
  --       apply (admissible.greq_Dia_iff_eq i a b).1,
  --       exact h,
  --     },
  --     case arrow: ρ τ ihρ ihτ {
  --       intros h,
  --       dsimp at h,
  --     }
  --   }
  -- end

  -- lemma eqext_dia_iff_eq {σ : 𝕋} (a b : ∥σ∥) (admissible : admissible_greq @greq) : 
  --   (∀ (x : (a ≅ b).𝕎) (y : (a ≅ b).ℂ), (a ≅ b).dia x y) ↔ a = b := 
  -- begin
  --   split,
  --   {
  --     induction σ,
  --     case zero {
  --       intros h,
  --       dsimp only [formula.ℂ, type.interpret, formula.dia, formula.𝕎, formula.eqext, formula.mwc] at *,
  --       exact h unit.star unit.star,
  --     },
  --     case ground: i {
  --       apply (admissible.greq_dia_iff_eq i a b).1,
  --     },
  --     case arrow: ρ τ ihρ ihτ {
  --       intros h,
  --       change ∀ z, _ at h, 
  --       ext u,
  --       specialize ihτ (a u) (b u),
  --       apply ihτ,
  --       intros x y, 
  --       specialize h (λ x, formula.𝕎_inh _),
  --       specialize h ⟨u, y⟩,
  --       dsimp only [formula.dia, formula.eqext] at h,
  --       have : x = formula.𝕎_inh _ := by {
  --         have := trivial_witness_eqext (a u) (b u) admissible,
  --         exact subsingleton_iff.mp this x (formula.eqext @greq (a u) (b u)).𝕎_inh,
  --       },
  --       rw ←this at h,
  --       apply h,
  --     }
  --   },
  --   {
  --     intros heq x y,
  --     subst heq,
  --     induction σ,
  --     case zero {
  --       dsimp, 
  --       refl,
  --     },
  --     case ground: i {
  --       have := (admissible.greq_dia_iff_eq i a a).2,
  --       apply this,
  --       refl,
  --     },
  --     case arrow: ρ τ ihρ ihτ {
  --       cases y, 
  --       dsimp only [formula.ℂ, formula.𝕎, formula.dia, formula.eqext, type.interpret, formula.mwc] at *, 
  --       solve_by_elim,
  --     },
  --   }
  -- end

  lemma eq_of_eqext_realizer {σ : 𝕋} (admissible : admissible_greq @greq) (a b : ∥σ∥) : dia.realizer (a ≅ b) → a = b := 
  begin 
    intros r,
    have p1 := Dia_of_realizer r,
    have p2 : (a ≅ b).is_gamma2 := gamma2_eqext _ _ admissible,
    have p3 := interpretation_of_gamma2_Dia p2 p1,
    exact (eqext_iff_eq _ _ admissible).1 p3,
  end

  
  


end eqext_in_relation_to_dialectica






