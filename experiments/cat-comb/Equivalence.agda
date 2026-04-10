---
--- Our main theorem: CC and CT coincide
---

open import Prelude
open import Ty
import CT
import CC

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
F (CT.coh ps τ σ) = CC.PSTm ps CC.[ FSub σ ]

F∼ (CT.eqv x) = CC.∼refl
F∼ {Γ = Γ} (CT.eq ps t u τ {σ = σ} {σ'} p) = subst₂ CC._∼_ (FSub≡ t σ) (FSub≡ u σ') ((CC.PSEq ps (F t) (F u)) CC.[ F∼Sub {Γ = Γ} p ]∼)
F∼ (CT.∼trans p q) = CC.∼trans (F∼ p) (F∼ q)

FSub {Γ' = ε} σ = tt
FSub {Γ' = Γ' ▹ A} (σ , t) = FSub σ , F t

FSub≡ (CT.var here) σ = refl
FSub≡ (CT.var (drop x)) (σ , t) = FSub≡ (CT.var x) σ
FSub≡ (CT.coh ps τ' σ') σ = CC.[∘] (CC.PSTm ps) (FSub σ') (FSub σ) ∙ cong (λ σ → CC.PSTm ps CC.[ σ ]) (FSub∘ σ' σ)

F∼Sub {Γ' = ε} p = tt
F∼Sub {Γ' = Γ' ▹ A} (p , q) = F∼Sub p , F∼ q

FSub∘ {Γ'' = ε} σ' σ = refl
FSub∘ {Γ'' = Γ'' ▹ A} (σ' , t') σ = Σ-≡,≡→≡ (FSub∘ σ' σ , substConst _ _ ∙ FSub≡ t' σ)

--- From CC to CT

G : {n : ℕ} {Γ : Con n} {A : Arr n} → CC.Tm Γ A → CT.Tm Γ A
G (CC.var x) = CT.var x
G CC.id = CT.id
G (f CC.· g) = CT.comp (G f) (G g)
G CC.term = CT.term
G (CC.pair f g) = CT.pair (G f) (G g)
G CC.fst = CT.fst
G CC.snd = CT.snd

G∼ : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : CC.Tm Γ A} → t CC.∼ u → G t CT.∼ G u
G∼ t = {!!}
-- G∼ (CC.Iβ t) = CT.apI (G t)
-- G∼ (CC.Kβ t u) = CT.apK (G t) (G u)
-- G∼ (CC.Sβ t u v) = CT.apS (G t) (G u) (G v)
-- G∼ CC.lamIβ = CT.lamIβ
-- G∼ CC.lamKβ = CT.lamKβ
-- G∼ CC.lamSβ = CT.lamSβ
-- G∼ CC.lamwk = CT.lamwk
-- G∼ CC.lamη = CT.lamη
-- G∼ (CC.∼$ p q) = CT.∼ap (G∼ p) (G∼ q)
-- G∼ CC.∼refl = CT.∼refl _
-- G∼ (CC.∼sym p) = CT.∼sym (G∼ p)
-- G∼ (CC.∼trans p q) = CT.∼trans (G∼ p) (G∼ q)

GSub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CC.Sub τ Γ Γ' → CT.Sub τ Γ Γ'
GSub {Γ' = ε} σ = tt
GSub {Γ' = Γ' ▹ A} (σ , t) = GSub σ , G t

GSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : CC.Tm Γ' A) {τ : SubTy n n'} (σ : CC.Sub τ Γ Γ') →
        ((G t) CT.[ GSub {Γ = Γ} σ ]) ≡ G (t CC.[ σ ])
-- GSub≡ (CC.var here) σ = refl
-- GSub≡ (CC.var (drop x)) (σ , t) = GSub≡ (CC.var x) σ
-- GSub≡ CC.I σ = refl
-- GSub≡ CC.K σ = refl
-- GSub≡ CC.S σ = refl
-- GSub≡ (t CC.$ u) σ = cong₂ CT.ap (GSub≡ t σ) (GSub≡ u σ)

--- F and G are mutually inverse functions

GF : {n : ℕ} {Γ : Con n} {A : Arr n} (t : CT.Tm Γ A) → G (F t) CT.∼ t
GFSub : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : CT.Sub τ Γ Γ') → GSub (FSub σ) CT.∼Sub σ

-- GF (CT.var x) = CT.∼refl _
-- GF (CT.coh ps τ σ) = CT.∼trans
  -- (CT.∼trans (CT.∼of≡ (sym (GSub≡ (CC.PSTm ps) (FSub σ)))) (G (CC.PSTm ps) CT.[ GFSub σ ]∼))
  -- (CT.∼trans (CT.eqs ps (G (CC.PSTm ps)) (CT.coh ps (SubTyId _) (CT.SubId _)) τ σ)
  -- (subst₂ CT._∼_ refl (cong (CT.coh ps τ) (CT.∘UnitL σ)) (CT.∼refl _)))

GFSub {Γ' = ε} tt = tt
GFSub {Γ' = Γ' ▹ A} (σ , t) = GFSub σ , GF t

FG : {n : ℕ} {Γ : Con n} {A : Arr n} (t : CC.Tm Γ A) → F (G t) CC.∼ t
-- FG (CC.var x) = CC.∼refl
-- FG {Γ = Γ} CC.I = CC.PSEq PS⊢X⇒X (CC.PSTm PS⊢X⇒X) CC.I CC.[ CC.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
-- FG {Γ = Γ} CC.K = CC.PSEq PS⊢X⇒Y⇒X (CC.PSTm PS⊢X⇒Y⇒X) CC.K CC.[ CC.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
-- FG {Γ = Γ} CC.S = CC.PSEq PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z (CC.PSTm PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z) CC.S CC.[ CC.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
-- FG (t CC.$ u) = CC.PSEq PSX⇒Y,X⊢Y (CC.PSTm PSX⇒Y,X⊢Y) (CC.var (drop here) CC.$ CC.var here) CC.[ (tt , FG t) , FG u ]∼
