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

--- Translation of contexts
--
-- A unary CL context is read as a context of global elements, and an arrow
-- context of CC is read as a context of exponentials.

Con'→Con : {n : ℕ} → Con' n → Con n
Con'→Con ε' = ε
Con'→Con (Γ ▹' A) = Con'→Con Γ ▹ (𝟙 , A)

∈'→∈ : {n : ℕ} {Γ : Con' n} {A : Ty n} → A ∈' Γ → (𝟙 , A) ∈ Con'→Con Γ
∈'→∈ here' = here
∈'→∈ (drop' x) = drop (∈'→∈ x)

Con→Con' : {n : ℕ} → Con n → Con' n
Con→Con' ε = ε'
Con→Con' (Γ ▹ (A , B)) = Con→Con' Γ ▹' (A ⇒ B)

∈→∈' : {n : ℕ} {Γ : Con n} {A B : Ty n} → (A , B) ∈ Γ → (A ⇒ B) ∈' Con→Con' Γ
∈→∈' here = here'
∈→∈' (drop {B = _ , _} x) = drop' (∈→∈' x)

--- From CL to CC

F : {n : ℕ} {Γ : Con' n} {A : Ty n} → CL.Tm Γ A → CC.Tm (Con'→Con Γ) (𝟙 , A)
F (CL.var x) = CC.var (∈'→∈ x)
F I  = abs snd
F K  = abs (abs (fst · snd))
F S  = abs (abs (abs (pair (pair (fst · fst · snd) snd · app)
                           (pair (fst · snd) snd · app) · app)))
F P₁ = abs (snd · fst)
F P₂ = abs (snd · snd)
F P  = abs (abs (pair (fst · snd) snd))
F T  = term
F (t $ u) = pair (F t) (F u) · app

--- From CC to CL
--
-- This is bracket abstraction: each categorical combinator is the CL term
-- which, applied to a point of the source, produces the corresponding point of
-- the target.

G : {n : ℕ} {Γ : Con n} {A B : Ty n} → CC.Tm Γ (A , B) → CL.Tm (Con→Con' Γ) (A ⇒ B)
G (CC.var x) = CL.var (∈→∈' x)
G id = I
G (f · g) = S $ (K $ G g) $ G f
G term = K $ T
G (pair f g) = S $ (S $ (K $ P) $ G f) $ G g
G fst = P₁
G snd = P₂
G (abs f) = S $ (K $ (S $ (K $ G f))) $ P
G app = S $ P₁ $ P₂

--- Auxiliary lemmas in CC

module _ {n : ℕ} {Γ : Con n} where

  open CC
  open CC.∼-Reasoning

  -- Composition distributes over pairing.
  pairComp : {X Y A B : Ty n} (e : Tm Γ (X , Y)) (u : Tm Γ (Y , A)) (v : Tm Γ (Y , B)) →
             e · pair u v ∼ pair (e · u) (e · v)
  pairComp e u v = begin∼
    e · pair u v
      ∼⟨ pext _ ⟩
    pair (e · pair u v · fst) (e · pair u v · snd)
      ∼⟨ ∼pair (assoc _ _ _) (assoc _ _ _) ⟩
    pair (e · (pair u v · fst)) (e · (pair u v · snd))
      ∼⟨ ∼pair (∼· ∼refl (pfst u v)) (∼· ∼refl (psnd u v)) ⟩
    pair (e · u) (e · v) ∎∼

  -- The general β-rule: applying an abstraction to an environment amounts to
  -- substituting.  `aβ` is the special case `h = fst`, `k = snd`.
  beta : {X A B C : Ty n} (f : Tm Γ (A × B , C)) (h : Tm Γ (X , A)) (k : Tm Γ (X , B)) →
         pair (h · abs f) k · app ∼ pair h k · f
  beta f h k = ∼sym (begin∼
    pair h k · f
      ∼⟨ ∼· ∼refl (∼sym (aβ f)) ⟩
    pair h k · (pair (fst · abs f) snd · app)
      ∼⟨ ∼sym (assoc _ _ _) ⟩
    pair h k · pair (fst · abs f) snd · app
      ∼⟨ ∼· (pairComp _ _ _) ∼refl ⟩
    pair (pair h k · (fst · abs f)) (pair h k · snd) · app
      ∼⟨ ∼· (∼pair (∼sym (assoc _ _ _)) (psnd h k)) ∼refl ⟩
    pair (pair h k · fst · abs f) k · app
      ∼⟨ ∼· (∼pair (∼· (pfst h k) ∼refl) ∼refl) ∼refl ⟩
    pair (h · abs f) k · app ∎∼)

  -- Same, for an abstraction sitting alone at the head of an application.
  beta' : {A B C : Ty n} (f : Tm Γ (A × B , C)) (k : Tm Γ (A , B)) →
          pair (abs f) k · app ∼ pair id k · f
  beta' f k = begin∼
    pair (abs f) k · app
      ∼⟨ ∼· (∼pair (∼sym (unitl _)) ∼refl) ∼refl ⟩
    pair (id · abs f) k · app
      ∼⟨ beta f id k ⟩
    pair id k · f ∎∼

  -- Composition distributes over application.
  appComp : {X Y A B : Ty n} (e : Tm Γ (X , Y)) (f : Tm Γ (Y , A ⇒ B)) (a : Tm Γ (Y , A)) →
            e · (pair f a · app) ∼ pair (e · f) (e · a) · app
  appComp e f a = ∼trans (∼sym (assoc _ _ _)) (∼· (pairComp e f a) ∼refl)

  -- Extensionality for maps into an exponential: it suffices to compare the
  -- two maps after applying them to a generic argument.
  funext : {A B C : Ty n} {f g : Tm Γ (A , B ⇒ C)} →
           pair (fst · f) snd · app ∼ pair (fst · g) snd · app → f ∼ g
  funext {f = f} {g = g} p = ∼trans (aext f) (∼trans (∼abs p) (∼sym (aext g)))

--- The translation F preserves the equivalence

module _ {n : ℕ} {Γ : Con' n} where

  open CC.∼-Reasoning

  -- F sends a pairing combinator to an actual pairing.
  FP : {A B : Ty n} (t : CL.Tm Γ A) (u : CL.Tm Γ B) →
       F (P $ t $ u) CC.∼ pair (F t) (F u)
  FP t u = begin∼
    pair (pair (F P) (F t) · app) (F u) · app
      ∼⟨ CC.∼· (CC.∼pair (beta' _ (F t)) CC.∼refl) CC.∼refl ⟩
    pair (pair id (F t) · abs (pair (fst · snd) snd)) (F u) · app
      ∼⟨ beta _ (pair id (F t)) (F u) ⟩
    pair (pair id (F t)) (F u) · pair (fst · snd) snd
      ∼⟨ pairComp _ _ _ ⟩
    pair (pair (pair id (F t)) (F u) · (fst · snd)) (pair (pair id (F t)) (F u) · snd)
      ∼⟨ CC.∼pair (CC.∼sym (CC.assoc _ _ _)) (CC.psnd _ _) ⟩
    pair (pair (pair id (F t)) (F u) · fst · snd) (F u)
      ∼⟨ CC.∼pair (CC.∼· (CC.pfst _ _) CC.∼refl) CC.∼refl ⟩
    pair (pair id (F t) · snd) (F u)
      ∼⟨ CC.∼pair (CC.psnd _ _) CC.∼refl ⟩
    pair (F t) (F u) ∎∼

  FP₁ : {A B : Ty n} (t : CL.Tm Γ (A × B)) → F (P₁ $ t) CC.∼ F t · fst
  FP₁ t = begin∼
    pair (F P₁) (F t) · app
      ∼⟨ beta' _ (F t) ⟩
    pair id (F t) · (snd · fst)
      ∼⟨ CC.∼sym (CC.assoc _ _ _) ⟩
    pair id (F t) · snd · fst
      ∼⟨ CC.∼· (CC.psnd _ _) CC.∼refl ⟩
    F t · fst ∎∼

  FP₂ : {A B : Ty n} (t : CL.Tm Γ (A × B)) → F (P₂ $ t) CC.∼ F t · snd
  FP₂ t = begin∼
    pair (F P₂) (F t) · app
      ∼⟨ beta' _ (F t) ⟩
    pair id (F t) · (snd · snd)
      ∼⟨ CC.∼sym (CC.assoc _ _ _) ⟩
    pair id (F t) · snd · snd
      ∼⟨ CC.∼· (CC.psnd _ _) CC.∼refl ⟩
    F t · snd ∎∼

  F∼ : {A : Ty n} {t u : CL.Tm Γ A} → t CL.∼ u → F t CC.∼ F u

  F∼ (CL.Iβ t) = begin∼
    pair (F I) (F t) · app
      ∼⟨ beta' snd (F t) ⟩
    pair id (F t) · snd
      ∼⟨ CC.psnd _ _ ⟩
    F t ∎∼

  F∼ (CL.Kβ t u) = begin∼
    pair (pair (F K) (F t) · app) (F u) · app
      ∼⟨ CC.∼· (CC.∼pair (beta' _ (F t)) CC.∼refl) CC.∼refl ⟩
    pair (pair id (F t) · abs (fst · snd)) (F u) · app
      ∼⟨ beta _ (pair id (F t)) (F u) ⟩
    pair (pair id (F t)) (F u) · (fst · snd)
      ∼⟨ CC.∼sym (CC.assoc _ _ _) ⟩
    pair (pair id (F t)) (F u) · fst · snd
      ∼⟨ CC.∼· (CC.pfst _ _) CC.∼refl ⟩
    pair id (F t) · snd
      ∼⟨ CC.psnd _ _ ⟩
    F t ∎∼

  F∼ (CL.Sβ t u v) = begin∼
    pair (pair (pair (F S) (F t) · app) (F u) · app) (F v) · app
      ∼⟨ CC.∼· (CC.∼pair (CC.∼· (CC.∼pair (beta' _ (F t)) CC.∼refl) CC.∼refl) CC.∼refl) CC.∼refl ⟩
    pair (pair (pair id (F t) · abs (abs _)) (F u) · app) (F v) · app
      ∼⟨ CC.∼· (CC.∼pair (beta _ (pair id (F t)) (F u)) CC.∼refl) CC.∼refl ⟩
    pair (pair (pair id (F t)) (F u) · abs _) (F v) · app
      ∼⟨ beta _ (pair (pair id (F t)) (F u)) (F v) ⟩
    e₃ · (pair (pair (fst · fst · snd) snd · app) (pair (fst · snd) snd · app) · app)
      ∼⟨ appComp e₃ _ _ ⟩
    pair (e₃ · (pair (fst · fst · snd) snd · app)) (e₃ · (pair (fst · snd) snd · app)) · app
      ∼⟨ CC.∼· (CC.∼pair (appComp e₃ _ _) (appComp e₃ _ _)) CC.∼refl ⟩
    pair (pair (e₃ · (fst · fst · snd)) (e₃ · snd) · app)
         (pair (e₃ · (fst · snd)) (e₃ · snd) · app) · app
      ∼⟨ CC.∼· (CC.∼pair (CC.∼· (CC.∼pair fstfstsnd (CC.psnd _ _)) CC.∼refl)
                         (CC.∼· (CC.∼pair fstsnd (CC.psnd _ _)) CC.∼refl)) CC.∼refl ⟩
    pair (pair (F t) (F v) · app) (pair (F u) (F v) · app) · app ∎∼
    where
      e₁ = pair id (F t)
      e₂ = pair e₁ (F u)
      e₃ = pair e₂ (F v)

      fstsnd : e₃ · (fst · snd) CC.∼ F u
      fstsnd = begin∼
        e₃ · (fst · snd)   ∼⟨ CC.∼sym (CC.assoc _ _ _) ⟩
        e₃ · fst · snd     ∼⟨ CC.∼· (CC.pfst _ _) CC.∼refl ⟩
        e₂ · snd           ∼⟨ CC.psnd _ _ ⟩
        F u ∎∼

      fstfstsnd : e₃ · (fst · fst · snd) CC.∼ F t
      fstfstsnd = begin∼
        e₃ · (fst · fst · snd)   ∼⟨ CC.∼sym (CC.assoc _ _ _) ⟩
        e₃ · (fst · fst) · snd   ∼⟨ CC.∼· (CC.∼sym (CC.assoc _ _ _)) CC.∼refl ⟩
        e₃ · fst · fst · snd     ∼⟨ CC.∼· (CC.∼· (CC.pfst _ _) CC.∼refl) CC.∼refl ⟩
        e₂ · fst · snd           ∼⟨ CC.∼· (CC.pfst _ _) CC.∼refl ⟩
        e₁ · snd                 ∼⟨ CC.psnd _ _ ⟩
        F t ∎∼

  F∼ (CL.P₁β t u) = begin∼
    F (P₁ $ (P $ t $ u))   ∼⟨ FP₁ (P $ t $ u) ⟩
    F (P $ t $ u) · fst    ∼⟨ CC.∼· (FP t u) CC.∼refl ⟩
    pair (F t) (F u) · fst ∼⟨ CC.pfst _ _ ⟩
    F t ∎∼

  F∼ (CL.P₂β t u) = begin∼
    F (P₂ $ (P $ t $ u))   ∼⟨ FP₂ (P $ t $ u) ⟩
    F (P $ t $ u) · snd    ∼⟨ CC.∼· (FP t u) CC.∼refl ⟩
    pair (F t) (F u) · snd ∼⟨ CC.psnd _ _ ⟩
    F u ∎∼

  F∼ (CL.Pη t) = begin∼
    F t
      ∼⟨ CC.pext (F t) ⟩
    pair (F t · fst) (F t · snd)
      ∼⟨ CC.∼pair (CC.∼sym (FP₁ t)) (CC.∼sym (FP₂ t)) ⟩
    pair (F (P₁ $ t)) (F (P₂ $ t))
      ∼⟨ CC.∼sym (FP (P₁ $ t) (P₂ $ t)) ⟩
    F (P $ (P₁ $ t) $ (P₂ $ t)) ∎∼

  F∼ (CL.Tη t) = CC.text (F t)

  -- The `lam*` rules.  Unlike the β/η rules above these are equations between
  -- *partially applied* S/K towers, so both sides translate to global elements
  -- of an exponential and cannot simply be β-reduced to a point: they have to
  -- be compared under `funext` above, after applying them to generic arguments.
  F∼ CL.lamIβ = {!!}
  F∼ CL.lamKβ = {!!}
  F∼ CL.lamSβ = {!!}
  F∼ CL.lamwk = {!!}
  F∼ CL.lamη = {!!}
  F∼ CL.lamP₁ = {!!}
  F∼ CL.lamP₂ = {!!}
  F∼ CL.lamP = {!!}
  F∼ CL.lamT = {!!}

  F∼ (CL.∼$ p q) = CC.∼· (CC.∼pair (F∼ p) (F∼ q)) CC.∼refl
  F∼ CL.∼refl = CC.∼refl
  F∼ (CL.∼sym p) = CC.∼sym (F∼ p)
  F∼ (CL.∼trans p q) = CC.∼trans (F∼ p) (F∼ q)

--- The translation G preserves the equivalence
--
-- This is the direction the `lam*` rules of CL exist for: each categorical
-- axiom becomes a closed S/K tower equation, applied to the translations of the
-- sub-terms and then normalised with `Sβ`/`Kβ`.

module _ {n : ℕ} {Γ : Con n} where

  open CL.∼-Reasoning

  -- η on the right: `lamη` applied to a single argument.
  etaR : {A B : Ty n} (h : CL.Tm (Con→Con' Γ) (A ⇒ B)) → (S $ (K $ h) $ I) CL.∼ h
  etaR h = CL.∼trans (CL.∼sym red) (CL.∼trans (CL.∼$ CL.lamη CL.∼refl) (CL.Iβ h))
    where
      red : (S $ (S $ (K $ S) $ K) $ (K $ I) $ h) CL.∼ (S $ (K $ h) $ I)
      red = begin∼
        S $ (S $ (K $ S) $ K) $ (K $ I) $ h
          ∼⟨ CL.Sβ _ _ _ ⟩
        S $ (K $ S) $ K $ h $ (K $ I $ h)
          ∼⟨ CL.∼$ (CL.Sβ _ _ _) (CL.Kβ _ _) ⟩
        K $ S $ h $ (K $ h) $ I
          ∼⟨ CL.∼$ (CL.∼$ (CL.Kβ _ _) CL.∼refl) CL.∼refl ⟩
        S $ (K $ h) $ I ∎∼

  G∼ : {A B : Ty n} {f g : CC.Tm Γ (A , B)} → f CC.∼ g → G f CL.∼ G g

  -- id · f ∼ f
  G∼ (CC.unitl f) = etaR (G f)

  -- f · id ∼ f
  G∼ (CC.unitr f) =
    CL.∼trans (CL.∼$ CL.lamIβ CL.∼refl) (CL.Iβ (G f))

  -- pair f g · fst ∼ f
  G∼ (CC.pfst f g) =
    CL.∼trans (CL.∼sym red)
      (CL.∼trans (CL.∼$ (CL.∼$ CL.lamP₁ CL.∼refl) CL.∼refl) (CL.Kβ (G f) (G g)))
    where
      red : (S $ (K $ (S $ (K $ (S $ (K $ P₁))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ G f $ G g)
            CL.∼ (S $ (K $ P₁) $ (S $ (S $ (K $ P) $ G f) $ G g))
      red = begin∼
        S $ (K $ (S $ (K $ (S $ (K $ P₁))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ G f $ G g
          ∼⟨ CL.∼$ (CL.Sβ _ _ _) CL.∼refl ⟩
        K $ (S $ (K $ (S $ (K $ P₁)))) $ G f $ (S $ (K $ S) $ (S $ (K $ P)) $ G f) $ G g
          ∼⟨ CL.∼$ (CL.∼$ (CL.Kβ _ _) (CL.Sβ _ _ _)) CL.∼refl ⟩
        S $ (K $ (S $ (K $ P₁))) $ (K $ S $ G f $ (S $ (K $ P) $ G f)) $ G g
          ∼⟨ CL.∼$ (CL.∼$ CL.∼refl (CL.∼$ (CL.Kβ _ _) CL.∼refl)) CL.∼refl ⟩
        S $ (K $ (S $ (K $ P₁))) $ (S $ (S $ (K $ P) $ G f)) $ G g
          ∼⟨ CL.Sβ _ _ _ ⟩
        K $ (S $ (K $ P₁)) $ G g $ (S $ (S $ (K $ P) $ G f) $ G g)
          ∼⟨ CL.∼$ (CL.Kβ _ _) CL.∼refl ⟩
        S $ (K $ P₁) $ (S $ (S $ (K $ P) $ G f) $ G g) ∎∼

  -- pair f g · snd ∼ g
  G∼ (CC.psnd f g) =
    CL.∼trans (CL.∼sym red)
      (CL.∼trans (CL.∼$ (CL.∼$ CL.lamP₂ CL.∼refl) CL.∼refl)
        (CL.∼trans (CL.∼$ (CL.Kβ I (G f)) CL.∼refl) (CL.Iβ (G g))))
    where
      red : (S $ (K $ (S $ (K $ (S $ (K $ P₂))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ G f $ G g)
            CL.∼ (S $ (K $ P₂) $ (S $ (S $ (K $ P) $ G f) $ G g))
      red = begin∼
        S $ (K $ (S $ (K $ (S $ (K $ P₂))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ G f $ G g
          ∼⟨ CL.∼$ (CL.Sβ _ _ _) CL.∼refl ⟩
        K $ (S $ (K $ (S $ (K $ P₂)))) $ G f $ (S $ (K $ S) $ (S $ (K $ P)) $ G f) $ G g
          ∼⟨ CL.∼$ (CL.∼$ (CL.Kβ _ _) (CL.Sβ _ _ _)) CL.∼refl ⟩
        S $ (K $ (S $ (K $ P₂))) $ (K $ S $ G f $ (S $ (K $ P) $ G f)) $ G g
          ∼⟨ CL.∼$ (CL.∼$ CL.∼refl (CL.∼$ (CL.Kβ _ _) CL.∼refl)) CL.∼refl ⟩
        S $ (K $ (S $ (K $ P₂))) $ (S $ (S $ (K $ P) $ G f)) $ G g
          ∼⟨ CL.Sβ _ _ _ ⟩
        K $ (S $ (K $ P₂)) $ G g $ (S $ (S $ (K $ P) $ G f) $ G g)
          ∼⟨ CL.∼$ (CL.Kβ _ _) CL.∼refl ⟩
        S $ (K $ P₂) $ (S $ (S $ (K $ P) $ G f) $ G g) ∎∼

  -- f ∼ pair (f · fst) (f · snd)
  G∼ (CC.pext f) = begin∼
    G f
      ∼⟨ CL.∼sym (CL.Iβ (G f)) ⟩
    I $ G f
      ∼⟨ CL.∼sym (CL.∼$ CL.lamP CL.∼refl) ⟩
    S $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁)))) $ (S $ (K $ P₂)) $ G f
      ∼⟨ CL.Sβ _ _ _ ⟩
    S $ (K $ S) $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁))) $ G f $ (S $ (K $ P₂) $ G f)
      ∼⟨ CL.∼$ (CL.Sβ _ _ _) CL.∼refl ⟩
    K $ S $ G f $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁)) $ G f) $ (S $ (K $ P₂) $ G f)
      ∼⟨ CL.∼$ (CL.∼$ (CL.Kβ _ _) (CL.Sβ _ _ _)) CL.∼refl ⟩
    S $ (K $ (S $ (K $ P)) $ G f $ (S $ (K $ P₁) $ G f)) $ (S $ (K $ P₂) $ G f)
      ∼⟨ CL.∼$ (CL.∼$ CL.∼refl (CL.∼$ (CL.Kβ _ _) CL.∼refl)) CL.∼refl ⟩
    S $ (S $ (K $ P) $ (S $ (K $ P₁) $ G f)) $ (S $ (K $ P₂) $ G f) ∎∼

  -- The remaining categorical axioms.

  -- Associativity of composition: needs
  --   S $ (K $ G h) $ (S $ (K $ G g) $ G f) ∼ S $ (K $ (S $ (K $ G h) $ G g)) $ G f
  -- `lamSβ` is the closed tower for this, but it is stated at
  -- (A ⇒ B ⇒ C ⇒ D) ⇒ … rather than at the composition types, so it does not
  -- apply directly; the tower probably has to be re-derived.
  G∼ (CC.assoc f g h) = {!!}

  -- NOT DERIVABLE as CL currently stands.  The goal is `G f ∼ K $ T` for an
  -- arbitrary f : Tm Γ (A , 𝟙), i.e. that every CL term of type A ⇒ 𝟙 is K $ T.
  -- `Tη` only gives this for terms of type 𝟙 itself, and `lamT : K $ T ∼ I` is
  -- confined to A = 𝟙 (it only typechecks at 𝟙 ⇒ 𝟙).  Closing this needs a new
  -- rule in CL.agda, and it cannot be a closed tower equation since it is a
  -- schema in the unknown f:
  --   lamT' : {A : Ty n} (h : Tm Γ (A ⇒ 𝟙)) → h ∼ K $ T
  G∼ (CC.text f) = {!!}

  -- The two exponential axioms: `lamKβ` / `lamwk` are the relevant towers.
  G∼ (CC.aβ f) = {!!}
  G∼ (CC.aext f) = {!!}

  -- Congruence and equivalence closure.
  G∼ (CC.∼· p q) = CL.∼$ (CL.∼$ CL.∼refl (CL.∼$ CL.∼refl (G∼ q))) (G∼ p)
  G∼ (CC.∼pair p q) = CL.∼$ (CL.∼$ CL.∼refl (CL.∼$ (CL.∼$ CL.∼refl CL.∼refl) (G∼ p))) (G∼ q)
  G∼ (CC.∼abs p) = CL.∼$ (CL.∼$ CL.∼refl (CL.∼$ CL.∼refl (CL.∼$ CL.∼refl (CL.∼$ CL.∼refl (G∼ p))))) CL.∼refl
  G∼ CC.∼refl = CL.∼refl
  G∼ (CC.∼sym p) = CL.∼sym (G∼ p)
  G∼ (CC.∼trans p q) = CL.∼trans (G∼ p) (G∼ q)

--- F and G are mutually inverse
--
-- Only on closed terms.  In an open context the round trip does not return to
-- its starting point on the nose: `Con→Con' (Con'→Con Γ)` replaces every type A
-- of Γ by `𝟙 ⇒ A`, so `G (F t)` and `t` do not even live in the same context.
-- For Γ = ε' (resp. ε) both translations of the context are the empty one and
-- the statements typecheck as expected.

-- A CL term is recovered from its global element by evaluating it at the point.
-- By induction on t; each combinator case unfolds to a closed tower (e.g.
-- G (F I) = S $ (K $ (S $ (K $ P₂))) $ P) whose reduction to I needs the same
-- `lam*` machinery as the holes above.
GF : {n : ℕ} {A : Ty n} (t : CL.Tm ε' A) → (G (F t) $ T) CL.∼ t
GF t = {!!}

-- A CC morphism is recovered from its name by uncurrying.
FG : {n : ℕ} {A B : Ty n} (f : CC.Tm ε (A , B)) → F (G f) CC.∼ abs (snd · f)
FG f = {!!}
