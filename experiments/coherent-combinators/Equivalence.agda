-- Equivalence between combinatory logic and categorical combinators
--
-- A CL term of type A is translated to a CC *global element* 𝟙 ⇒ A: CC only
-- builds arrow-typed terms, so there is no CC term of type 𝟙 or of an atomic
-- type to receive `T` or an application. Conversely a CC morphism is translated
-- to a CL term of the same (arrow) type by bracket abstraction, and turned back
-- into a point by applying it to `T`.

open import Prelude
open import Ty
import CL
import CC

open CC using (_·_ ; pair ; fst ; snd ; abs ; app ; id ; term)
open CL using (_$_ ; I ; K ; S ; P₁ ; P₂ ; P ; T)

--- From CL to CC

F : {n : ℕ} {Γ : Con n} {A : Ty n} → CL.Tm Γ A → CC.Tm Γ (𝟙 ⇒ A)
F (CL.var x) = CC.var x
F CL.I = abs snd
F CL.K = abs (abs (fst · snd))
F CL.S = abs (abs (abs (pair (pair (fst · fst · snd) snd · app) (pair (fst · snd) snd · app) · app)))
F CL.P₁ = abs (snd · fst)
F CL.P₂ = abs (snd · snd)
F CL.P = abs (abs (pair (fst · snd) snd))
F CL.T = term
F (t CL.$ u) = pair (F t) (F u) · app

--- From CC to CL

G : {n : ℕ} {Γ : Con n} {A : Ty n} → CC.Tm Γ A → CL.Tm Γ A
G (CC.var x) = K $ CL.var x
G CC.id = I
G (f CC.· g) = S $ (K $ G g) $ G f
G CC.term = K $ T
G (CC.pair f g) = S $ (S $ (K $ P) $ G f) $ G g
G CC.fst = P₁
G CC.snd = P₂
G (CC.abs f) = S $ (K $ (S $ (K $ G f))) $ P
G CC.app = S $ P₁ $ P₂

-- a CC point 𝟙 ⇒ A, seen as a CL term of type A
G• : {n : ℕ} {Γ : Con n} {A : Ty n} → CC.Tm Γ (𝟙 ⇒ A) → CL.Tm Γ A
G• f = G f $ T

--- How G computes on arguments. These are all pure β (Iβ/Kβ/Sβ/P₁β/P₂β): the
--- bracket abstractions in G were chosen so that applying them to an argument
--- unwinds without any need for extensionality.

module _ {n : ℕ} {Γ : Con n} where

  open CL.∼-Reasoning

  G· : {A B C : Ty n} (f : CC.Tm Γ (A ⇒ B)) (g : CC.Tm Γ (B ⇒ C)) (a : CL.Tm Γ A) →
       G (f · g) $ a CL.∼ G g $ (G f $ a)
  G· f g a = begin∼
    S $ (K $ G g) $ G f $ a   ∼⟨ CL.Sβ _ _ _ ⟩
    (K $ G g $ a) $ (G f $ a) ∼⟨ CL.∼$ (CL.Kβ _ _) CL.∼refl ⟩
    G g $ (G f $ a)           ∎∼

  Gpair : {Z A B : Ty n} (f : CC.Tm Γ (Z ⇒ A)) (g : CC.Tm Γ (Z ⇒ B)) (a : CL.Tm Γ Z) →
          G (pair f g) $ a CL.∼ P $ (G f $ a) $ (G g $ a)
  Gpair f g a = begin∼
    S $ (S $ (K $ P) $ G f) $ G g $ a       ∼⟨ CL.Sβ _ _ _ ⟩
    (S $ (K $ P) $ G f $ a) $ (G g $ a)     ∼⟨ CL.∼$ (CL.Sβ _ _ _) CL.∼refl ⟩
    ((K $ P $ a) $ (G f $ a)) $ (G g $ a)   ∼⟨ CL.∼$ (CL.∼$ (CL.Kβ _ _) CL.∼refl) CL.∼refl ⟩
    P $ (G f $ a) $ (G g $ a)               ∎∼

  Gabs : {A B C : Ty n} (f : CC.Tm Γ (A × B ⇒ C)) (a : CL.Tm Γ A) (b : CL.Tm Γ B) →
         G (abs f) $ a $ b CL.∼ G f $ (P $ a $ b)
  Gabs f a b = begin∼
    S $ (K $ (S $ (K $ G f))) $ P $ a $ b       ∼⟨ CL.∼$ (CL.Sβ _ _ _) CL.∼refl ⟩
    (K $ (S $ (K $ G f)) $ a) $ (P $ a) $ b     ∼⟨ CL.∼$ (CL.∼$ (CL.Kβ _ _) CL.∼refl) CL.∼refl ⟩
    S $ (K $ G f) $ (P $ a) $ b                 ∼⟨ CL.Sβ _ _ _ ⟩
    (K $ G f $ b) $ (P $ a $ b)                 ∼⟨ CL.∼$ (CL.Kβ _ _) CL.∼refl ⟩
    G f $ (P $ a $ b)                           ∎∼

  Gapp : {A B : Ty n} (p : CL.Tm Γ ((A ⇒ B) × A)) →
         G CC.app $ p CL.∼ (P₁ $ p) $ (P₂ $ p)
  Gapp p = CL.Sβ _ _ _

  -- G (abs f) as a point, partially applied: this is the shape GF has to face
  GabsT : {A B : Ty n} (f : CC.Tm Γ (𝟙 × A ⇒ B)) →
          G• (abs f) CL.∼ S $ (K $ G f) $ (P $ T)
  GabsT f = begin∼
    S $ (K $ (S $ (K $ G f))) $ P $ T     ∼⟨ CL.Sβ _ _ _ ⟩
    (K $ (S $ (K $ G f)) $ T) $ (P $ T)   ∼⟨ CL.∼$ (CL.Kβ _ _) CL.∼refl ⟩
    S $ (K $ G f) $ (P $ T)               ∎∼

--- The translations preserve the equivalences

F∼ : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : CL.Tm Γ A} → t CL.∼ u → F t CC.∼ F u
F∼ = {!!}

G∼ : {n : ℕ} {Γ : Con n} {A : Ty n} {f g : CC.Tm Γ A} → f CC.∼ g → G f CL.∼ G g
G∼ = {!!}

--- F and G are mutually inverse

GF : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CL.Tm Γ A) → G• (F t) CL.∼ t
GF = {!!}

FG : {n : ℕ} {Γ : Con n} {A : Ty n} (f : CC.Tm Γ (𝟙 ⇒ A)) → F (G• f) CC.∼ f
FG = {!!}
