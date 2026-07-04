---
--- Our main theorem: CL and CT coincide
---

open import Prelude
open import Ty
import CT
import CL

--- From CT to CL

F     : {n : ℕ} {Γ : Con n} {A : Ty n} → CT.Tm Γ A → CL.Tm Γ A
F∼    : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : CT.Tm Γ A} → t CT.∼ u → F t CL.∼ F u
FSub  : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CT.Sub τ Γ Γ' → CL.Sub τ Γ Γ'
FSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : CT.Tm Γ' A) {τ : SubTy n n'} (σ : CT.Sub τ Γ Γ') →
        ((F t) CL.[ FSub {Γ = Γ} σ ]) ≡ F (t CT.[ σ ])
F∼Sub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : CT.Sub τ Γ Γ'} → σ CT.∼Sub σ' → FSub σ CL.∼Sub FSub σ'
FSub∘ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (σ' : CT.Sub τ' Γ' Γ'') (σ : CT.Sub τ Γ Γ') →
        FSub σ' CL.∘ FSub σ ≡ FSub {Γ = Γ} (CT._∘_ {Γ = Γ} σ' σ)

F (CT.var x) = CL.var x
F (CT.coh ps τ σ) = CL.PSTm ps CL.[ FSub σ ]

F∼ (CT.eqv x) = CL.∼refl
F∼ {Γ = Γ} (CT.eq ps t u τ {σ = σ} {σ'} p) = subst₂ CL._∼_ (FSub≡ t σ) (FSub≡ u σ') ((CL.PSEq ps (F t) (F u)) CL.[ F∼Sub {Γ = Γ} p ]∼)
F∼ (CT.∼trans p q) = CL.∼trans (F∼ p) (F∼ q)

FSub {Γ' = ε} σ = tt
FSub {Γ' = Γ' ▹ A} (σ , t) = FSub σ , F t

FSub≡ (CT.var here) σ = refl
FSub≡ (CT.var (drop x)) (σ , t) = FSub≡ (CT.var x) σ
FSub≡ (CT.coh ps τ' σ') σ = CL.[∘] (CL.PSTm ps) (FSub σ') (FSub σ) ∙ cong (λ σ → CL.PSTm ps CL.[ σ ]) (FSub∘ σ' σ)

F∼Sub {Γ' = ε} p = tt
F∼Sub {Γ' = Γ' ▹ A} (p , q) = F∼Sub p , F∼ q

FSub∘ {Γ'' = ε} tt σ = refl
FSub∘ {Γ'' = Γ'' ▹ A} (σ' , t') σ = Σ-≡,≡→≡ (FSub∘ σ' σ , substConst _ _ ∙ FSub≡ t' σ)

--- From CL to CT

G : {n : ℕ} {Γ : Con n} {A : Ty n} → CL.Tm Γ A → CT.Tm Γ A
G {n} {Γ} (CL.var x) = CT.var x
G {n} {Γ} CL.I = CT.I
G {n} {Γ} CL.K = CT.K
G {n} {Γ} CL.S = CT.S
G (t CL.$ u) = CT.ap (G t) (G u)

G∼ : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : CL.Tm Γ A} → t CL.∼ u → G t CT.∼ G u
G∼ (CL.Iβ t) = CT.apI (G t)
G∼ (CL.Kβ t u) = CT.apK (G t) (G u)
G∼ (CL.Sβ t u v) = CT.apS (G t) (G u) (G v)
G∼ CL.lamIβ = CT.lamIβ
G∼ CL.lamKβ = CT.lamKβ
G∼ CL.lamSβ = CT.lamSβ
G∼ CL.lamwk = CT.lamwk
G∼ CL.lamη = CT.lamη
G∼ (CL.∼$ p q) = CT.∼ap (G∼ p) (G∼ q)
G∼ CL.∼refl = CT.∼refl _
G∼ (CL.∼sym p) = CT.∼sym (G∼ p)
G∼ (CL.∼trans p q) = CT.∼trans (G∼ p) (G∼ q)

GSub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CL.Sub τ Γ Γ' → CT.Sub τ Γ Γ'
GSub {Γ' = ε} σ = tt
GSub {Γ' = Γ' ▹ A} (σ , t) = GSub σ , G t

GSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : CL.Tm Γ' A) {τ : SubTy n n'} (σ : CL.Sub τ Γ Γ') →
        ((G t) CT.[ GSub {Γ = Γ} σ ]) ≡ G (t CL.[ σ ])
GSub≡ (CL.var here) σ = refl
GSub≡ (CL.var (drop x)) (σ , t) = GSub≡ (CL.var x) σ
GSub≡ CL.I σ = refl
GSub≡ CL.K σ = refl
GSub≡ CL.S σ = refl
GSub≡ (t CL.$ u) σ = cong₂ CT.ap (GSub≡ t σ) (GSub≡ u σ)

--- F and G are mutually inverse functions

GF : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CT.Tm Γ A) → G (F t) CT.∼ t
GFSub : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : CT.Sub τ Γ Γ') → GSub (FSub σ) CT.∼Sub σ

GF (CT.var x) = CT.∼refl _
GF (CT.coh ps τ σ) = CT.∼trans
  (CT.∼trans (CT.∼of≡ (sym (GSub≡ (CL.PSTm ps) (FSub σ)))) (G (CL.PSTm ps) CT.[ GFSub σ ]∼))
  (CT.∼trans
    (CT.eqs ps (G (CL.PSTm ps)) (CT.coh ps (SubTyId _) (CT.SubId _)) τ σ)
    (subst₂ CT._∼_ refl (cong (CT.coh ps τ) (CT.∘UnitL σ)) (CT.∼refl _))
  )

GFSub {Γ' = ε} tt = tt
GFSub {Γ' = Γ' ▹ A} (σ , t) = GFSub σ , GF t

FG : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CL.Tm Γ A) → F (G t) CL.∼ t
FG (CL.var x) = CL.∼refl
FG {Γ = Γ} CL.I = CL.PSEq PS⊢X⇒X (CL.PSTm PS⊢X⇒X) CL.I CL.[ CL.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
FG {Γ = Γ} CL.K = CL.PSEq PS⊢X⇒Y⇒X (CL.PSTm PS⊢X⇒Y⇒X) CL.K CL.[ CL.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
FG {Γ = Γ} CL.S = CL.PSEq PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z (CL.PSTm PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z) CL.S CL.[ CL.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
FG (t CL.$ u) = CL.PSEq PSX⇒Y,X⊢Y (CL.PSTm PSX⇒Y,X⊢Y) (CL.var (drop here) CL.$ CL.var here) CL.[ (tt , FG t) , FG u ]∼
