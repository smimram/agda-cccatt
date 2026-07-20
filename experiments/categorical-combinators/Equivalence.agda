---
--- Our main theorem: CC and CT coincide
---

open import Prelude
open import Ty
open import PS
import CT
import CC
import CCPS

--- From CT to CC

F     : {n : ℕ} {Γ : Con n} {A : Arr n} → CT.Tm Γ A → CC.Tm Γ A
F∼    : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : CT.Tm Γ A} → t CT.∼ u → F t CC.∼ F u
FSub  : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CT.Sub τ Γ Γ' → CC.Sub τ Γ Γ'
FSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : CT.Tm Γ' A) {τ : SubTy n n'} (σ : CT.Sub τ Γ Γ') →
        ((F t) CC.[ FSub {Γ = Γ} σ ]) ≡ F (t CT.[ σ ])
F∼Sub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : CT.Sub τ Γ Γ'} → σ CT.∼Sub σ' → FSub σ CC.∼Sub FSub σ'
FSub∘ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (σ' : CT.Sub τ' Γ' Γ'') (σ : CT.Sub τ Γ Γ') →
        FSub σ' CC.∘ FSub σ ≡ FSub {Γ = Γ} (CT._∘_ {Γ = Γ} σ' σ)

F (CT.var x) = CC.var x
F (CT.coh ps τ σ) = CCPS.PSTm ps CC.[ FSub σ ]

F∼ (CT.eqv x) = CC.∼refl
F∼ {Γ = Γ} (CT.eq ps t u τ {σ = σ} {σ'} p) = subst₂ CC._∼_ (FSub≡ t σ) (FSub≡ u σ') ((CCPS.PSEq ps (F t) (F u)) CC.[ F∼Sub {Γ = Γ} p ]∼)
F∼ (CT.∼trans p q) = CC.∼trans (F∼ p) (F∼ q)

FSub {Γ' = ε} σ = tt
FSub {Γ' = Γ' ▹ A} (σ , t) = FSub σ , F t

FSub≡ (CT.var here) σ = refl
FSub≡ (CT.var (drop x)) (σ , t) = FSub≡ (CT.var x) σ
FSub≡ (CT.coh ps τ' σ') σ = CC.[∘] (CCPS.PSTm ps) (FSub σ') (FSub σ) ∙ cong (λ σ → CCPS.PSTm ps CC.[ σ ]) (FSub∘ σ' σ)

F∼Sub {Γ' = ε} p = tt
F∼Sub {Γ' = Γ' ▹ A} (p , q) = F∼Sub p , F∼ q

FSub∘ {Γ'' = ε} σ' σ = refl
FSub∘ {Γ'' = Γ'' ▹ A} (σ' , t') σ = Σ-≡,≡→≡ (FSub∘ σ' σ , substConst _ _ ∙ FSub≡ t' σ)

--- From CC to CT

-- Every derived operation of CT is a coherence, so that G is defined by
-- sending each combinator to its CT counterpart
G : {n : ℕ} {Γ : Con n} {A : Arr n} → CC.Tm Γ A → CT.Tm Γ A
G (CC.var x) = CT.var x
G CC.id = CT.id
G (f CC.· g) = CT.comp (G f) (G g)
G CC.term = CT.term
G (CC.pair f g) = CT.pair (G f) (G g)
G CC.fst = CT.fst
G CC.snd = CT.snd
G (CC.abs f) = CT.abs (G f)
G CC.app = CT.app

-- ... and every axiom of CC holds in CT, being an instance of the
-- contractibility of a pasting scheme
G∼ : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : CC.Tm Γ A} → t CC.∼ u → G t CT.∼ G u
G∼ (CC.pfst f g) = CT.pfst (G f) (G g)
G∼ (CC.psnd f g) = CT.psnd (G f) (G g)
G∼ (CC.pext f) = CT.pext (G f)
G∼ (CC.text f) = CT.text (G f)
G∼ (CC.aβ f) = CT.aβ (G f)
G∼ (CC.aext f) = CT.aext (G f)
G∼ (CC.unitl f) = CT.unitl (G f)
G∼ (CC.unitr f) = CT.unitr (G f)
G∼ (CC.assoc f g h) = CT.assoc (G f) (G g) (G h)
G∼ (CC.∼· p q) = CT.∼· (G∼ p) (G∼ q)
G∼ (CC.∼pair p q) = CT.∼pair (G∼ p) (G∼ q)
G∼ (CC.∼abs p) = CT.∼abs (G∼ p)
G∼ CC.∼refl = CT.∼refl (G _)
G∼ (CC.∼sym p) = CT.∼sym (G∼ p)
G∼ (CC.∼trans p q) = CT.∼trans (G∼ p) (G∼ q)

GSub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CC.Sub τ Γ Γ' → CT.Sub τ Γ Γ'
GSub {Γ' = ε} σ = tt
GSub {Γ' = Γ' ▹ A} (σ , t) = GSub σ , G t

-- G is natural: all the combinators are coherences over the *empty*
-- substitution but for their arguments, so this is a plain congruence
GSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : CC.Tm Γ' A) {τ : SubTy n n'} (σ : CC.Sub τ Γ Γ') →
        ((G t) CT.[ GSub {Γ = Γ} σ ]) ≡ G (t CC.[ σ ])
GSub≡ (CC.var here) (σ , t) = refl
GSub≡ (CC.var (drop x)) (σ , t) = GSub≡ (CC.var x) σ
GSub≡ CC.id σ = refl
GSub≡ (f CC.· g) σ = cong₂ CT.comp (GSub≡ f σ) (GSub≡ g σ)
GSub≡ CC.term σ = refl
GSub≡ (CC.pair f g) σ = cong₂ CT.pair (GSub≡ f σ) (GSub≡ g σ)
GSub≡ CC.fst σ = refl
GSub≡ CC.snd σ = refl
GSub≡ (CC.abs f) σ = cong CT.abs (GSub≡ f σ)
GSub≡ CC.app σ = refl

--- F and G are mutually inverse functions

GF : {n : ℕ} {Γ : Con n} {A : Arr n} (t : CT.Tm Γ A) → G (F t) CT.∼ t
GFSub : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : CT.Sub τ Γ Γ') → GSub (FSub σ) CT.∼Sub σ

GF (CT.var x) = CT.∼refl _
GF (CT.coh ps τ σ) = CT.∼trans
  -- G (F (coh ps τ σ)) is G of the canonical term of ps, substituted by σ
  (CT.∼trans (CT.∼of≡ (sym (GSub≡ (CCPS.PSTm ps) (FSub σ)))) (G (CCPS.PSTm ps) CT.[ GFSub σ ]∼))
  -- ... which is equivalent to any other term of ps, in particular to the
  -- generic coherence, whose substitution by σ is coh ps τ σ back again
  (CT.∼trans (CT.eqs ps (G (CCPS.PSTm ps)) (CT.coh ps (SubTyId _) (CT.SubId _)) τ σ)
             (CT.∼of≡ (cong (CT.coh ps τ) (CT.∘UnitL σ))))

GFSub {Γ' = ε} tt = tt
GFSub {Γ' = Γ' ▹ A} (σ , t) = GFSub σ , GF t

-- Every combinator is the canonical term of its defining pasting scheme, up to
-- the equivalence generated by contractibility
Fcoh∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A B : Ty n'} (ps : PSArr Γ' (A , B)) {τ : SubTy n n'}
        (σ : CC.Sub τ Γ Γ') (t : CC.Tm Γ' (A , B)) → CCPS.PSTm ps CC.[ σ ] CC.∼ t CC.[ σ ]
Fcoh∼ ps σ t = CCPS.PSEq ps (CCPS.PSTm ps) t CC.[ CC.∼SubRefl σ ]∼

FG : {n : ℕ} {Γ : Con n} {A : Arr n} (t : CC.Tm Γ A) → F (G t) CC.∼ t
FG (CC.var x) = CC.∼refl
FG CC.id = Fcoh∼ PS⊢X⇒X {τ = SubTy1 _} tt CC.id
FG (f CC.· g) = CC.∼trans
  (Fcoh∼ PSX⇒Y,Y⇒Z⊢X⇒Z {τ = SubTy3 _ _ _} _ (CC.var (drop here) CC.· CC.var here))
  (CC.∼· (FG f) (FG g))
FG CC.term = Fcoh∼ PS⊢X⇒𝟙 {τ = SubTy1 _} tt CC.term
FG (CC.pair f g) = CC.∼trans
  (Fcoh∼ PSX⇒Y,X⇒Z⊢X⇒Y×Z {τ = SubTy3 _ _ _} _ (CC.pair (CC.var (drop here)) (CC.var here)))
  (CC.∼pair (FG f) (FG g))
FG CC.fst = Fcoh∼ PS⊢X×Y⇒X {τ = SubTy2 _ _} tt CC.fst
FG CC.snd = Fcoh∼ PS⊢X×Y⇒Y {τ = SubTy2 _ _} tt CC.snd
FG (CC.abs f) = CC.∼trans
  (Fcoh∼ PSX×Y⇒Z⊢X⇒Y⇒Z {τ = SubTy3 _ _ _} _ (CC.abs (CC.var here)))
  (CC.∼abs (FG f))
FG CC.app = Fcoh∼ PS⊢[X⇒Y]×X⇒Y {τ = SubTy2 _ _} tt CC.app
