import proof


section realizers 

  variables {Î¹ : Type}  {gri : ground_interpretation Î¹} 
  local notation `ð½` := formula Î¹ gri
  local notation `ð` := type Î¹ gri
  variables {greq : Î  {i : Î¹}, â¥ð i // gri â¥ â â¥ð i // gri â¥ â ð½}
  local infixr `â` : 35 := formula.eqext @greq

  namespace dia 


  section logical_axioms 

    open formula

    variables {Ï Ï : ð}
    variables (A B C : ð½) (P : â¥Ïâ¥ â ð½)
    variables (Î : premises Î¹ gri)

    def and_contr : realizer (A â¹ A â A) :=
      subtype.mk
        (â¨(Î» x y, if A.dia x y.fst then y.2 else y.1), (Î» x, (x, x))â©)
        (begin
          rintros â¨yâ, â¨yââ, yâââ©â© h,
          simp only [dia, dite_eq_ite, id.def] at *,
          by_cases h' : A.dia yâ yââ,
          {
            simp only [*, if_true] at h,
            exact â¨h', hâ©,
          },
          {
            simp only [*, if_false] at h,
            contradiction,
          },
        end)
    
    def or_contr : realizer (A â A â¹ A) :=
      subtype.mk
      ((Î» x y, (y, y)), (Î» x, match x with | (sum.inl x') := x' | (sum.inr x') := x' end)) 
      (begin 
        rintros â¨yâ, yââ© h,
        cases yâ;
        assumption,
      end)

    def and_weak : realizer (A â B â¹ A) := 
      subtype.mk 
      (prod.mk (Î» â¨y1, y2â© y3, (y3, â_inh B)) (Î» â¨y1, y2â©, y1))
      (begin 
        rintros â¨â¨yââ, yâââ© , yââ© â¨hâ, hââ©,
        assumption,
      end)

    def or_weak : realizer (A â¹ A â B) :=
      subtype.mk 
      ((Î» x y, y.fst), (Î» x, sum.inl x))
      (begin 
        intros y h,
        assumption,
      end)

    def exfalso : realizer (prime false â¹ A) :=
      subtype.mk 
      â¨(Î» _ _, punit.star), (Î» _, ð_inh A)â©
      (begin 
        intros y h,
        cases h,
      end)

    def and_perm : realizer (A â B â¹ B â A) :=
      subtype.mk 
      (((Î» x y, (y.2, y.1)), Î» x, (x.2, x.1)))
      (begin 
        rintros â¨â¨yââ, yâââ©, â¨yââ, yâââ©â© h,
        dsimp only [dia] at *,
        exact and.comm.mp h,
      end)

    def or_perm : realizer (A â B â¹ B â A) :=
      subtype.mk 
      (((Î» x y, y.swap), (Î» x, x.swap)))
      (begin 
        rintros â¨yâ, â¨yââ, yâââ©â© h, 
        cases yâ;
        assumption,
      end)
    
    def univ_ax : Î  a : â¥Ïâ¥, realizer (universal' Ï P â¹ P a) :=
      Î» a, 
      subtype.mk 
      (((Î» x y, â¨_, yâ©), (Î» x, x a))) 
      (begin 
        intros y h,
        exact h,
      end)

    def exist_ax : Î  a : â¥Ïâ¥, realizer (P a â¹ existential' Ï P) :=
      Î» a,
      subtype.mk
      (((Î» x y, y a x), (Î» x, â¨a, xâ©)))
      (begin 
        intros y h,
        exact h,
      end)

  end logical_axioms


  section logical_rules 

    open formula 

    local attribute [simp] dia

    variables {Î : premises Î¹ gri}
    variables {Ï Ï : ð} 
    variables {A B C : ð½} {P : â¥Ïâ¥ â ð½}

    def of_prime_true {p : Prop} [decp : decidable p] (hp : p) : realizer (@prime _ gri p decp) := 
      subtype.mk 
      unit.star 
      (Î» _, hp)

    def mp : realizer A â realizer (A â¹ B) â realizer B :=
      Î» hA hAB, subtype.mk 
      ((hAB).1.2 (hA).1)
      (begin 
        intros y,
        let hâ := (hA).2,
        let hâ := (hAB).2, 
        dsimp only [dia, â, mwc, dia, ð] at hâ,
        simp only [prod.forall, subtype.val_eq_coe] at hâ,
        apply hâ,
        apply hâ,
      end)

    def syl : realizer (A â¹ B) â realizer (B â¹ C) â realizer (A â¹ C) := 
      Î» hAB hBC, subtype.mk 
      ((Î» x y, (hAB).1.1 x ((hBC).1.1 ((hAB).1.2 x) y)), (Î» x, (hBC).1.2 ((hAB).1.2 x)))
      (begin 
        intros y h,
        let hâ := (hAB).2,
        let hâ := (hBC).2,
        dsimp only [â, mwc, dia, ð] at hâ hâ,
        simp only [prod.forall, subtype.val_eq_coe] at hâ hâ,
        apply hâ,
        apply hâ,
        apply h,
      end)

    def exportation : realizer (A â B â¹ C) â realizer (A â¹ (B â¹ C)) :=
      Î» h, subtype.mk
      (((Î» x y, ((h).1.1 (x, y.1) y.2).1), (Î» x, ((Î» y z, ((h).1.1 (x, y) z).2), (Î» y, (h).1.2 (x, y)))))) 
      (begin
        rintros â¨yâ, â¨yââ, yâââ©â©,
        let h' := (h).2,
        intros hâ hâ,
        dsimp only [formula.â, formula.ð, formula.dia, formula.mwc] at *,
        simp only [prod.forall] at *,
        exact h' _ _ _ â¨hâ, hââ©,
      end)

    def importation : realizer (A â¹ (B â¹ C)) â realizer (A â B â¹ C) := 
      Î» h, subtype.mk 
      (((Î» x y, ((h).1.1 x.1 (x.2, y), ((h).1.2 x.1).1 x.2 y)), (Î» x, ((h).1.2 x.1).2 x.2)))
      (begin 
        rintros â¨â¨yââ, yâââ©, yââ©,
        let h' := (h).2,
        rintros hâ,
        dsimp only [â, mwc, dia, ð] at h' hâ â¢,
        simp only [prod.forall, subtype.val_eq_coe] at h' hâ â¢,
        specialize h' yââ â¨yââ, yââ©,
        apply h',
        { apply hâ.1, },
        { apply hâ.2, },
      end)

    def univ_rule : (Î  x : â¥Ïâ¥, realizer (A â¹ P x)) â realizer (A â¹ universal' Ï P) :=
      Î» h, subtype.mk 
      ((Î» x y, (h y.1).1.1 x y.2), (Î» x y, (h y).1.2 x))
      (begin 
        rintros â¨y1, â¨z, y2â©â©,
        let ht := (h z).property,
        specialize ht â¨y1, y2â©,
        exact ht,
      end)

    def exist_rule : (Î  x : â¥Ïâ¥, realizer (P x â¹ A)) â realizer (existential' Ï P â¹ A) :=
      Î» h, subtype.mk 
      (((Î» x y z v, (h z).1.1 v y), (Î» x, (h x.1).1.2 x.2)))
      (begin 
        rintros â¨â¨y1, y2â©, y3â©,
        let ht := (h y1).property,
        specialize ht â¨y2, y3â©,
        exact ht,  
      end)

    
    def expansion : realizer (A â¹ B) â realizer ((C â A) â¹ (C â B)) :=
      Î» h, subtype.mk 
        (prod.mk
          (Î» x y, 
            match x with 
            | (sum.inl x') := (y.1, ((h).1.1 (ð_inh _) y.2))
            | (sum.inr x') := (y.1, (h).1.1 x' y.2)
            end
          )
          (Î» x, 
            match x with 
            | (sum.inl x') := sum.inl x'
            | (sum.inr x') := sum.inr ((h).1.2 x')
            end
          )
        )
        (begin
          rintros â¨yâ, â¨yââ, yâââ©â©,
          let h' := (h).property,
          dsimp only [â, mwc, dia, ð] at *,
          intros hA,
          cases yâ,
          case sum.inl 
          { assumption, },
          case sum.inr 
          { dsimp only [mwc, realizer, dia] at *, 
            simp only [prod.forall, subtype.val_eq_coe] at *, 
            solve_by_elim, },
        end)
        
      
    def qfer (admissible : admissible_greq @greq) (a b : â¥Ïâ¥) : realizer (a â b) â realizer (P a â¹ P b) :=
      Î» h, subtype.mk 
      ( have eqab : a = b := eq_of_eqext_realizer admissible _ _ h, 
        have eqâ : (P a).â = (P b).â := congr_arg â (congr_arg P eqab),
        have eqð : (P a).ð = (P b).ð := congr_arg ð (congr_arg P eqab),
        prod.mk 
          (Î» u v, cast (eq.symm eqâ) v) 
          (Î» u, cast eqð u))
      (begin 
        intros y h',
        have eqab : a = b := eq_of_eqext_realizer admissible _ _ h,
        subst eqab,
        exact h',
      end)

  end logical_rules

  section induction_rule 

    open formula

    def ir {A : â¥ð // griâ¥ â ð½} (m : â¥ð // griâ¥) :
       realizer (A nat.zero) â (Î  n : â¥ð // griâ¥, realizer (A n â¹ A n.succ)) â realizer (A m) :=
    Î» h0 hi, subtype.mk 
      (nat.rec_on m h0.val (Î» n p, (hi n).val.snd p)) 
      (begin
        intros y,
        induction m,
        case zero {
          exact h0.2 y,
        },
        case succ: m ih{
          have := Î» n, (hi n).property,
          dsimp only [â, mwc, ð] at this,
          simp only [dia] at this,
          simp only,
          set u : (A m).ð := nat.rec h0.val (Î» (n : â), (hi n).val.snd) m,
          specialize this m,
          specialize this â¨u, yâ©,
          apply this,
          apply ih,
        }
      end)

  end induction_rule

  section other 

    open formula 
    
    def markov {Ï : ð} (A : â¥Ïâ¥ â ð½) 
      [uw : â x : â¥Ïâ¥, subsingleton (A x).ð]
      [uc : â x : â¥Ïâ¥, subsingleton (A x).â] :
      realizer (â¼(ââ (x : â¥Ïâ¥) , â¼(A x)) â¹ (ââ (x : â¥Ïâ¥) , A x)) :=
      subtype.mk 
        (prod.mk (Î» _ _, â_inh _) (Î» h, â¨(h.1 (ð_inh _) (â_inh _)).1, ð_inh _â©)) 
        (begin
          dsimp only [negation, â, mwc, dia] at *,
          simp only [â, prod.forall, ð] at *,
          intros y u v h,
          set Ï := (((y, u), v).fst.fst (ââ (x : â¥Ïâ¥), A xâ¹(falsum Î¹ gri)).ð_inh (falsum Î¹ gri).â_inh).fst,
          set Ïâ := ((ââ (x : â¥Ïâ¥), A xâ¹(falsum Î¹ gri))â¹(falsum Î¹ gri)).â_inh.fst with eq_Ïâ,
          rw âeq_Ïâ at *,
          set Ïâ := ((ââ (x : â¥Ïâ¥), A xâ¹(falsum Î¹ gri))â¹(falsum Î¹ gri)).â_inh.snd with eq_Ïâ,
          rw âeq_Ïâ at *,
          set Ï := ((y, u), v) with eq_Ï,
          rw âeq_Ï at *,
          dsimp only at h,
          have : Ï = (y Ïâ Ïâ).fst := rfl,
          rw this, clear this,
          rw [imp_false, imp_false, dia_not_not] at h,
          have : (Ï.fst.fst Ïâ Ïâ).snd.fst = (A (Ï.fst.fst Ïâ Ïâ).fst).ð_inh := 
            subsingleton_iff.mp (uw (Ï.fst.fst Ïâ Ïâ).fst) _ _,
          rw âthis, clear this,
          have : 
            (Ïâ (Ï.fst.fst Ïâ Ïâ).fst).fst (Ï.fst.fst Ïâ Ïâ).snd.fst (Ï.fst.fst Ïâ Ïâ).snd.snd 
            = 
            v (Ï.fst.fst Ïâ Ïâ).fst (Ï.fst.fst Ïâ Ïâ).snd.fst :=
            subsingleton_iff.mp (uc (Ï.fst.fst Ïâ Ïâ).fst) _ _,
          rw âthis, clear this,
          apply h,
        end)

    def ip {Ï Ï : ð} (A : â¥Ïâ¥ â ð½) (B : â¥Ïâ¥ â ð½)
      [uwA : â x : â¥Ïâ¥, subsingleton (A x).ð] 
      [ucB : â y : â¥Ïâ¥, subsingleton (B y).â] :
      realizer $ ((ââ (x : â¥Ïâ¥) , A x) â¹ (ââ (y : â¥Ïâ¥) , B y)) â¹ ââ (y : â¥Ïâ¥) , ((ââ (x : â¥Ïâ¥) , A x) â¹ B y) :=
      subtype.mk 
        (let f := Î» x : â¥Ïâ¥, ð_inh (A x) in 
        let g := Î» (y : â¥Ïâ¥) (w : ð (B y)), â_inh (B y) in 
        prod.mk
          (Î» x y, (f, g))
          (Î» a, â¨(a.2 f).1, ((Î» z _, a.1 f g), (Î» z, (a.2 f).2))â©)
        )
        (begin 
          dsimp only [â, mwc, dia, ð] at *,
          simp only [â, prod.forall, ð] at *,
          intros x y u hâ,
          unfreezingI { dsimp only at *},
          set a := x (Î» (x : Ï.interpret), (A x).ð_inh) (Î» (y : Ï.interpret) (w : (B y).mwc.fst), (B y).â_inh) with eq_a,
          rw âeq_a at *,
          set b := y (Î» (x : Ï.interpret), (A x).ð_inh) with eq_b,
          rw âeq_b at *,
          set c := Î» (z : Î  (x : Ï.interpret), (A x).mwc.fst), b.snd with eq_c,
          rw âeq_c at *,
          intros hâ,
          have : (u b.fst (Î» (z : Î  (x : Ï.interpret), (A x).mwc.fst) (á¾° : (B b.fst).mwc.snd), a, c)).snd = â_inh (B b.fst) := 
            subsingleton_iff.mp (ucB b.fst) _ _,
          rw this, clear this,
          have : (u b.fst (Î» (z : Î  (x : Ï.interpret), (A x).mwc.fst) (á¾° : (B b.fst).mwc.snd), a, c)).fst a.fst = ð_inh (A a.fst) 
            := subsingleton_iff.mp (uwA a.fst) _ _,
          rw this at hâ, clear this,
          apply hâ,
          exact hâ,
        end)

    def qfac {Ï Ï : ð} (A : â¥Ïâ¥ â â¥Ïâ¥ â ð½) 
      [uw : â x y, subsingleton (A x y).ð] [uc : â x y, subsingleton (A x y).â] :
      realizer $ (ââ x : â¥Ïâ¥, ââ y : â¥Ïâ¥, A x y â¹ ââ Y : â¥Ï â£ Ïâ¥, ââ x : â¥Ïâ¥, A x (Y x)) :=
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

  variables {Î¹ : Type}  {gri : ground_interpretation Î¹}
  local notation `ð½` := formula Î¹ gri
  variables {greq : Î  {i : Î¹}, â¥ð i // griâ¥ â â¥ð i // griâ¥ â ð½}
  variables (admissible : admissible_greq @greq)

  include admissible

  def dia_realize {Î : premises Î¹ gri} (premise_realizer : (Î  {Î³ : ð½}, Î³ â Î â dia.realizer Î³)) : 
  Î  {A : ð½}, proof @greq {with_markov := tt, with_ip := tt} Î A â dia.realizer A
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
  | _ (univ_rule prf) := dia.univ_rule $ Î» x, (prf x).dia_realize
  | _ (exist_rule prf) := dia.exist_rule $ Î» x, (prf x).dia_realize
  | _ (ir m prf_0 prf_succ) := dia.ir m prf_0.dia_realize $ Î» n, (prf_succ n).dia_realize
  | _ (qfer Ï x y A prf) := dia.qfer admissible x y prf.dia_realize
  | _ (@markov _ _ _ _ _ Ï A uw uc _) := @dia.markov _ _ _ A uw uc
  | _ (@ip _ _ _ _ _ _ _ A B uwA ucB _) := @dia.ip _ _ _ _ A B uwA ucB

  end proof
end soundness