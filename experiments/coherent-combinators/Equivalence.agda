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

  --- Generalized combinator laws for the images of the CL combinators.
  --
  -- `ap` is CC's counterpart of CL application on points (of any base object X);
  -- `F (t $ u)` is definitionally `ap (F t) (F u)`.  Each law lets the combinator
  -- sit under an arbitrary environment `e : X → 𝟙`, so that after `funext`
  -- pushes projections in front of `F c`, the projection composite is absorbed
  -- into `e`.  These are the `F∼ (Iβ/Kβ/Sβ/…)` proofs generalised from F-images
  -- to arbitrary points.

  ap : {X A B : Ty n} → Tm Γ (X , A ⇒ B) → Tm Γ (X , A) → Tm Γ (X , B)
  ap f a = pair f a · app

  -- `ap` commutes with precomposition (this is `appComp`).
  ap· : {X Y A B : Ty n} (e : Tm Γ (X , Y)) (f : Tm Γ (Y , A ⇒ B)) (a : Tm Γ (Y , A)) →
        e · ap f a ∼ ap (e · f) (e · a)
  ap· = appComp

  -- F I = abs snd
  iβ : {X A : Ty n} (e : Tm Γ (X , 𝟙)) (p : Tm Γ (X , A)) →
       ap (e · abs snd) p ∼ p
  iβ e p = ∼trans (beta snd e p) (psnd e p)

  -- F P₁ = abs (snd · fst),  F P₂ = abs (snd · snd)
  p₁β : {X A B : Ty n} (e : Tm Γ (X , 𝟙)) (p : Tm Γ (X , A × B)) →
        ap (e · abs (snd · fst)) p ∼ p · fst
  p₁β e p = ∼trans (beta (snd · fst) e p)
                   (∼trans (∼sym (assoc _ _ _)) (∼· (psnd e p) ∼refl))

  p₂β : {X A B : Ty n} (e : Tm Γ (X , 𝟙)) (p : Tm Γ (X , A × B)) →
        ap (e · abs (snd · snd)) p ∼ p · snd
  p₂β e p = ∼trans (beta (snd · snd) e p)
                   (∼trans (∼sym (assoc _ _ _)) (∼· (psnd e p) ∼refl))

  -- F K = abs (abs (fst · snd))
  kβ : {X A B : Ty n} (e : Tm Γ (X , 𝟙)) (p : Tm Γ (X , A)) (q : Tm Γ (X , B)) →
       ap (ap (e · abs (abs (fst · snd))) p) q ∼ p
  kβ e p q =
    ∼trans (∼· (∼pair (beta (abs (fst · snd)) e p) ∼refl) ∼refl)
      (∼trans (beta (fst · snd) (pair e p) q)
        (∼trans (∼sym (assoc _ _ _))
          (∼trans (∼· (pfst (pair e p) q) ∼refl) (psnd e p))))

  -- F P = abs (abs (pair (fst · snd) snd))
  pβ : {X A B : Ty n} (e : Tm Γ (X , 𝟙)) (p : Tm Γ (X , A)) (q : Tm Γ (X , B)) →
       ap (ap (e · abs (abs (pair (fst · snd) snd))) p) q ∼ pair p q
  pβ e p q =
    ∼trans (∼· (∼pair (beta (abs (pair (fst · snd) snd)) e p) ∼refl) ∼refl)
      (∼trans (beta (pair (fst · snd) snd) (pair e p) q)
        (∼trans (pairComp _ _ _)
          (∼pair (∼trans (∼sym (assoc _ _ _)) (∼trans (∼· (pfst (pair e p) q) ∼refl) (psnd e p)))
                 (psnd (pair e p) q))))

  -- F S = abs (abs (abs (pair (pair (fst · fst · snd) snd · app)
  --                           (pair (fst · snd) snd · app) · app)))
  sβ : {X A B C : Ty n} (e : Tm Γ (X , 𝟙))
       (p : Tm Γ (X , A ⇒ B ⇒ C)) (q : Tm Γ (X , A ⇒ B)) (r : Tm Γ (X , A)) →
       ap (ap (ap (e · abs (abs (abs (pair (pair (fst · fst · snd) snd · app)
                                          (pair (fst · snd) snd · app) · app)))) p) q) r
       ∼ ap (ap p r) (ap q r)
  sβ {A = A} {B = B} {C = C} e p q r = begin∼
    ap (ap (ap (e · abs (abs (abs BODY))) p) q) r
      ∼⟨ ∼· (∼pair (∼· (∼pair (beta (abs (abs BODY)) e p) ∼refl) ∼refl) ∼refl) ∼refl ⟩
    ap (ap (e1 · abs (abs BODY)) q) r
      ∼⟨ ∼· (∼pair (beta (abs BODY) e1 q) ∼refl) ∼refl ⟩
    ap (e2 · abs BODY) r
      ∼⟨ beta BODY e2 r ⟩
    e3 · BODY
      ∼⟨ ap· e3 _ _ ⟩
    ap (e3 · ap (fst · fst · snd) snd) (e3 · ap (fst · snd) snd)
      ∼⟨ ∼· (∼pair (ap· e3 _ _) (ap· e3 _ _)) ∼refl ⟩
    ap (ap (e3 · (fst · fst · snd)) (e3 · snd)) (ap (e3 · (fst · snd)) (e3 · snd))
      ∼⟨ ∼· (∼pair (∼· (∼pair red-ffs (psnd e2 r)) ∼refl)
                   (∼· (∼pair red-fs (psnd e2 r)) ∼refl)) ∼refl ⟩
    ap (ap p r) (ap q r) ∎∼
    where
      e1 = pair e p ; e2 = pair e1 q ; e3 = pair e2 r
      BODY : Tm Γ ((((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A) , C)
      BODY = pair (pair (fst · fst · snd) snd · app) (pair (fst · snd) snd · app) · app

      red-ffs : e3 · (fst · fst · snd) ∼ p
      red-ffs = ∼trans (∼sym (assoc _ _ _))
                  (∼trans (∼· (∼sym (assoc _ _ _)) ∼refl)
                    (∼trans (∼· (∼· (pfst e2 r) ∼refl) ∼refl)
                      (∼trans (∼· (pfst e1 q) ∼refl) (psnd e p))))

      red-fs : e3 · (fst · snd) ∼ q
      red-fs = ∼trans (∼sym (assoc _ _ _)) (∼trans (∼· (pfst e2 r) ∼refl) (psnd e1 q))

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

  -- The `lam*` rules (including the terminal's `lamText`).  Unlike the β/η rules
  -- above these are equations between *partially applied* S/K towers, so both
  -- sides translate to global elements of an exponential and cannot simply be
  -- β-reduced to a point: they have to be compared under `funext` above, after
  -- applying them to generic arguments.
  -- S (K I) ∼ I.  Two funexts introduce a generic function g = fst · snd and a
  -- generic argument a = snd (over Θ = (𝟙 × (A⇒B)) × A); both towers reduce to
  -- `ap g a` by the generalized combinator laws.
  F∼ CL.lamIβ = funext (funext (CC.∼trans redL (CC.∼sym redR)))
    where
      e = fst · fst ; g = fst · snd ; a = snd

      redR : ap (fst · ap (fst · F I) snd) snd CC.∼ ap g a
      redR = CC.∼· (CC.∼pair (CC.∼· CC.∼refl (iβ fst snd)) CC.∼refl) CC.∼refl

      redL : ap (fst · ap (fst · F (S $ (K $ I))) snd) snd CC.∼ ap g a
      redL = begin∼
        ap (fst · ap (fst · ap (F S) (ap (F K) (F I))) snd) snd
          ∼⟨ CC.∼· (CC.∼pair (CC.∼· CC.∼refl
               (CC.∼· (CC.∼pair (ap· fst (F S) (ap (F K) (F I))) CC.∼refl) CC.∼refl)) CC.∼refl) CC.∼refl ⟩
        ap (fst · ap (ap (fst · F S) (fst · ap (F K) (F I))) snd) snd
          ∼⟨ CC.∼· (CC.∼pair (CC.∼· CC.∼refl
               (CC.∼· (CC.∼pair (CC.∼· (CC.∼pair CC.∼refl (ap· fst (F K) (F I))) CC.∼refl) CC.∼refl) CC.∼refl)) CC.∼refl) CC.∼refl ⟩
        ap (fst · ap (ap (fst · F S) (ap (fst · F K) (fst · F I))) snd) snd
          ∼⟨ CC.∼· (CC.∼pair (ap· fst (ap (fst · F S) (ap (fst · F K) (fst · F I))) snd) CC.∼refl) CC.∼refl ⟩
        ap (ap (fst · ap (fst · F S) (ap (fst · F K) (fst · F I))) (fst · snd)) snd
          ∼⟨ CC.∼· (CC.∼pair (CC.∼· (CC.∼pair (ap· fst (fst · F S) (ap (fst · F K) (fst · F I))) CC.∼refl) CC.∼refl) CC.∼refl) CC.∼refl ⟩
        ap (ap (ap (fst · (fst · F S)) (fst · ap (fst · F K) (fst · F I))) g) snd
          ∼⟨ CC.∼· (CC.∼pair (CC.∼· (CC.∼pair (CC.∼· (CC.∼pair (CC.∼sym (CC.assoc fst fst (F S)))
               (ap· fst (fst · F K) (fst · F I))) CC.∼refl) CC.∼refl) CC.∼refl) CC.∼refl) CC.∼refl ⟩
        ap (ap (ap (e · F S) (ap (fst · (fst · F K)) (fst · (fst · F I)))) g) a
          ∼⟨ CC.∼· (CC.∼pair (CC.∼· (CC.∼pair (CC.∼· (CC.∼pair CC.∼refl
               (CC.∼· (CC.∼pair (CC.∼sym (CC.assoc fst fst (F K))) (CC.∼sym (CC.assoc fst fst (F I)))) CC.∼refl))
               CC.∼refl) CC.∼refl) CC.∼refl) CC.∼refl) CC.∼refl ⟩
        ap (ap (ap (e · F S) (ap (e · F K) (e · F I))) g) a
          ∼⟨ sβ e (ap (e · F K) (e · F I)) g a ⟩
        ap (ap (ap (e · F K) (e · F I)) a) (ap g a)
          ∼⟨ CC.∼· (CC.∼pair (kβ e (e · F I) a) CC.∼refl) CC.∼refl ⟩
        ap (e · F I) (ap g a)
          ∼⟨ iβ e (ap g a) ⟩
        ap g a ∎∼
  -- The remaining `lam*` cases follow the exact recipe worked out for `lamIβ`
  -- and `lamText` above: apply CC `funext` once per arrow of the type (2 for
  -- lamη/lamP, 3 for lamKβ/lamwk/lamP₁/lamP₂, 4 for lamSβ), push the projections
  -- `funext` introduces through the `F`-application tree with `ap·`/`assoc`, and
  -- reduce both towers to a common normal form with the generalized combinator
  -- laws `iβ`/`kβ`/`sβ`/`pβ`/`p₁β`/`p₂β`.  Each is only bookkeeping, but the
  -- congruence nesting is long (lamSβ especially), so they are left open.
  F∼ CL.lamKβ = {!!}
  F∼ CL.lamSβ = {!!}
  F∼ CL.lamwk = {!!}
  F∼ CL.lamη = {!!}
  F∼ CL.lamP₁ = {!!}
  F∼ CL.lamP₂ = {!!}
  F∼ CL.lamP = {!!}
  -- After two CC funexts the goal is between two maps into 𝟙, and `text` makes
  -- both equal to `term`.
  F∼ CL.lamText = funext (funext (CC.∼trans (CC.text _) (CC.∼sym (CC.text _))))

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

  G∼ : {A B : Ty n} {f g : CC.Tm Γ (A , B)} → f CC.∼ g → G f CL.∼ G g

  -- id · f ∼ f
  G∼ (CC.unitl f) = CL.etaR (G f)

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

  -- The remaining categorical axioms.  Each is discharged with CL's functional
  -- extensionality (`CL.funext`): apply both towers to a fresh variable,
  -- normalise with the β/product rules, and compare.  This is exactly the use
  -- the `lam*` family of CL was built to support.

  -- Associativity of composition.
  G∼ (CC.assoc f g h) = CL.funext (CL.∼trans redL (CL.∼sym redR))
    where
      gf = CL.wk (G f) ; gg = CL.wk (G g) ; gh = CL.wk (G h) ; x = CL.var here'

      redL : (S $ (K $ gh) $ (S $ (K $ gg) $ gf) $ x) CL.∼ (gh $ (gg $ (gf $ x)))
      redL = CL.∼trans (CL.comp$ gh (S $ (K $ gg) $ gf) x)
                       (CL.∼$ CL.∼refl (CL.comp$ gg gf x))

      redR : (S $ (K $ (S $ (K $ gh) $ gg)) $ gf $ x) CL.∼ (gh $ (gg $ (gf $ x)))
      redR = CL.∼trans (CL.comp$ (S $ (K $ gh) $ gg) gf x)
                       (CL.comp$ gh gg (gf $ x))

  -- pair (fst · abs f) snd · app ∼ f
  G∼ (CC.aβ f) = CL.funext (CL.∼trans redL (CL.∼sym redR))
    where
      gf = CL.wk (G f) ; x = CL.var here'

      -- Both sides applied to x reduce to `gf $ (P $ (P₁ $ x) $ (P₂ $ x))`.
      target = gf $ (P $ (P₁ $ x) $ (P₂ $ x))

      redL : (S $ (K $ (S $ P₁ $ P₂))
                $ (S $ (S $ (K $ P) $ (S $ (K $ (S $ (K $ (S $ (K $ gf))) $ P)) $ P₁)) $ P₂)
                $ x) CL.∼ target
      redL = begin∼
        S $ (K $ (S $ P₁ $ P₂))
          $ (S $ (S $ (K $ P) $ (S $ (K $ (S $ (K $ (S $ (K $ gf))) $ P)) $ P₁)) $ P₂) $ x
          ∼⟨ CL.comp$ (S $ P₁ $ P₂) _ x ⟩
        (S $ P₁ $ P₂) $ (S $ (S $ (K $ P) $ (S $ (K $ (S $ (K $ (S $ (K $ gf))) $ P)) $ P₁)) $ P₂ $ x)
          ∼⟨ CL.∼$ CL.∼refl (CL.pair$ (S $ (K $ (S $ (K $ (S $ (K $ gf))) $ P)) $ P₁) P₂ x) ⟩
        (S $ P₁ $ P₂) $ (P $ (S $ (K $ (S $ (K $ (S $ (K $ gf))) $ P)) $ P₁ $ x) $ (P₂ $ x))
          ∼⟨ CL.∼$ CL.∼refl (CL.∼$ (CL.∼$ CL.∼refl (CL.comp$ (S $ (K $ (S $ (K $ gf))) $ P) P₁ x)) CL.∼refl) ⟩
        (S $ P₁ $ P₂) $ (P $ (S $ (K $ (S $ (K $ gf))) $ P $ (P₁ $ x)) $ (P₂ $ x))
          ∼⟨ CL.∼$ CL.∼refl (CL.∼$ (CL.∼$ CL.∼refl (CL.comp$ (S $ (K $ gf)) P (P₁ $ x))) CL.∼refl) ⟩
        (S $ P₁ $ P₂) $ (P $ (S $ (K $ gf) $ (P $ (P₁ $ x))) $ (P₂ $ x))
          ∼⟨ CL.app$ (P $ (S $ (K $ gf) $ (P $ (P₁ $ x))) $ (P₂ $ x)) ⟩
        P₁ $ (P $ (S $ (K $ gf) $ (P $ (P₁ $ x))) $ (P₂ $ x))
          $ (P₂ $ (P $ (S $ (K $ gf) $ (P $ (P₁ $ x))) $ (P₂ $ x)))
          ∼⟨ CL.∼$ (CL.P₁β _ _) (CL.P₂β _ _) ⟩
        (S $ (K $ gf) $ (P $ (P₁ $ x))) $ (P₂ $ x)
          ∼⟨ CL.comp$ gf (P $ (P₁ $ x)) (P₂ $ x) ⟩
        gf $ (P $ (P₁ $ x) $ (P₂ $ x)) ∎∼

      redR : (gf $ x) CL.∼ target
      redR = CL.∼$ CL.∼refl (CL.Pη x)

  -- f ∼ abs (pair (fst · f) snd · app)
  --
  -- Unlike `aβ`, the two sides have an *arrow* result type A ⇒ (B ⇒ C), so a
  -- single `funext` still leaves an arrow: apply `funext` twice, introducing two
  -- fresh variables x0 : A and x1 : B, then normalise as in `aβ`.  No `Tη` is
  -- used, so this closes with no new CL rule.
  G∼ (CC.aext f) = CL.funext (CL.funext (CL.∼sym redR))
    where
      gf = CL.wk (CL.wk (G f))
      x0 = CL.var (drop' here') ; x1 = CL.var here'
      w = P $ x0 $ x1
      Gb = S $ (K $ (S $ P₁ $ P₂)) $ (S $ (S $ (K $ P) $ (S $ (K $ gf) $ P₁)) $ P₂)

      redR : (S $ (K $ (S $ (K $ Gb))) $ P $ x0 $ x1) CL.∼ (gf $ x0 $ x1)
      redR = begin∼
        S $ (K $ (S $ (K $ Gb))) $ P $ x0 $ x1
          ∼⟨ CL.∼$ (CL.comp$ (S $ (K $ Gb)) P x0) CL.∼refl ⟩
        (S $ (K $ Gb)) $ (P $ x0) $ x1
          ∼⟨ CL.comp$ Gb (P $ x0) x1 ⟩
        Gb $ w
          ∼⟨ CL.comp$ (S $ P₁ $ P₂) (S $ (S $ (K $ P) $ (S $ (K $ gf) $ P₁)) $ P₂) w ⟩
        (S $ P₁ $ P₂) $ (S $ (S $ (K $ P) $ (S $ (K $ gf) $ P₁)) $ P₂ $ w)
          ∼⟨ CL.∼$ CL.∼refl (CL.pair$ (S $ (K $ gf) $ P₁) P₂ w) ⟩
        (S $ P₁ $ P₂) $ (P $ (S $ (K $ gf) $ P₁ $ w) $ (P₂ $ w))
          ∼⟨ CL.∼$ CL.∼refl (CL.∼$ (CL.∼$ CL.∼refl (CL.comp$ gf P₁ w)) CL.∼refl) ⟩
        (S $ P₁ $ P₂) $ (P $ (gf $ (P₁ $ w)) $ (P₂ $ w))
          ∼⟨ CL.app$ (P $ (gf $ (P₁ $ w)) $ (P₂ $ w)) ⟩
        P₁ $ (P $ (gf $ (P₁ $ w)) $ (P₂ $ w)) $ (P₂ $ (P $ (gf $ (P₁ $ w)) $ (P₂ $ w)))
          ∼⟨ CL.∼$ (CL.P₁β _ _) (CL.P₂β _ _) ⟩
        (gf $ (P₁ $ w)) $ (P₂ $ w)
          ∼⟨ CL.∼$ (CL.∼$ CL.∼refl (CL.P₁β x0 x1)) (CL.P₂β x0 x1) ⟩
        gf $ x0 $ x1 ∎∼

  -- f ∼ term.  `G f : A ⇒ 𝟙`, so this is exactly `lamTη`, the terminal's `lam*`
  -- rule -- the bracket abstraction of this very `text` axiom.
  G∼ (CC.text f) = CL.lamTη (G f)

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
-- By induction on t: the application case is a pure β-computation (`evApp`), and
-- each combinator case reduces its closed tower to the combinator via CL's
-- functional extensionality.
module _ {n : ℕ} where

  open CL
  open CL.∼-Reasoning {Γ = ε' {n}}

  -- Evaluating the image of an application: G of a CC application, applied to the
  -- point, is the two evaluated points applied.  No funext -- pure β.
  evApp : {A B : Ty n} (a : CC.Tm ε (𝟙 , A ⇒ B)) (b : CC.Tm ε (𝟙 , A)) →
          (G (CC.pair a b CC.· CC.app) $ T) ∼ (G a $ T) $ (G b $ T)
  evApp a b = begin∼
    S $ (K $ (S $ P₁ $ P₂)) $ (S $ (S $ (K $ P) $ G a) $ G b) $ T
      ∼⟨ Sβ _ _ _ ⟩
    K $ (S $ P₁ $ P₂) $ T $ (S $ (S $ (K $ P) $ G a) $ G b $ T)
      ∼⟨ ∼$ (Kβ _ _) ∼refl ⟩
    (S $ P₁ $ P₂) $ (S $ (S $ (K $ P) $ G a) $ G b $ T)
      ∼⟨ ∼$ ∼refl (Sβ _ _ _) ⟩
    (S $ P₁ $ P₂) $ ((S $ (K $ P) $ G a $ T) $ (G b $ T))
      ∼⟨ ∼$ ∼refl (∼$ (Sβ _ _ _) ∼refl) ⟩
    (S $ P₁ $ P₂) $ ((K $ P $ T $ (G a $ T)) $ (G b $ T))
      ∼⟨ ∼$ ∼refl (∼$ (∼$ (Kβ _ _) ∼refl) ∼refl) ⟩
    (S $ P₁ $ P₂) $ ((P $ (G a $ T)) $ (G b $ T))
      ∼⟨ Sβ _ _ _ ⟩
    P₁ $ (P $ (G a $ T) $ (G b $ T)) $ (P₂ $ (P $ (G a $ T) $ (G b $ T)))
      ∼⟨ ∼$ (P₁β _ _) (P₂β _ _) ⟩
    (G a $ T) $ (G b $ T) ∎∼

  GF : {A : Ty n} (t : CL.Tm ε' A) → (G (F t) $ T) ∼ t

  GF T = Kβ T T

  GF I = ∼trans redI (CL.funext (∼trans redz (∼sym (Iβ (var here')))))
    where
      redI : (G (F I) $ T) ∼ (S $ (K $ P₂) $ (P $ T))
      redI = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

      redz : (wk (S $ (K $ P₂) $ (P $ T)) $ var here') ∼ var here'
      redz = ∼trans (Sβ _ _ _) (∼trans (∼$ (Kβ _ _) ∼refl) (P₂β _ _))

  GF P₁ = ∼trans redP₁ (CL.funext redz)
    where
      redP₁ : (G (F P₁) $ T) ∼ (S $ (K $ (S $ (K $ P₁) $ P₂)) $ (P $ T))
      redP₁ = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

      redz : (wk (S $ (K $ (S $ (K $ P₁) $ P₂)) $ (P $ T)) $ var here') ∼ (P₁ $ var here')
      redz = ∼trans (Sβ _ _ _) (∼trans (∼$ (Kβ _ _) ∼refl)
               (∼trans (Sβ _ _ _) (∼trans (∼$ (Kβ _ _) ∼refl) (∼$ ∼refl (P₂β _ _)))))

  GF P₂ = ∼trans redP₂ (CL.funext redz)
    where
      redP₂ : (G (F P₂) $ T) ∼ (S $ (K $ (S $ (K $ P₂) $ P₂)) $ (P $ T))
      redP₂ = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

      redz : (wk (S $ (K $ (S $ (K $ P₂) $ P₂)) $ (P $ T)) $ var here') ∼ (P₂ $ var here')
      redz = ∼trans (Sβ _ _ _) (∼trans (∼$ (Kβ _ _) ∼refl)
               (∼trans (Sβ _ _ _) (∼trans (∼$ (Kβ _ _) ∼refl) (∼$ ∼refl (P₂β _ _)))))

  -- Same recipe as I/P₁/P₂ but with much larger towers: `G (F K)`, `G (F S)`,
  -- `G (F P)` are deep nests of `S $ (K $ (S $ (K $ …))) $ P` (one layer per
  -- `abs` in F c).  Reduce `G (F c) $ T` applied to the combinator's arity of
  -- fresh variables (2 for K/P, 3 for S) with `Sβ`/`Kβ`/`P₁β`/`P₂β`, closing
  -- under `funext` (twice for K/P, three times for S).  Left open: mechanical
  -- but long.
  GF K = {!!}
  GF S = {!!}
  GF P = {!!}

  GF (t $ u) = ∼trans (evApp (F t) (F u)) (∼$ (GF t) (GF u))

-- A CC morphism is recovered from its name (uncurried): `F (G f)` is the point
-- naming `f`, i.e. the curry of `f` precomposed with 𝟙 × A ≅ A.
module _ {n : ℕ} where

  open CC
  open CC.∼-Reasoning {Γ = ε {n}}

  FG : {A B : Ty n} (f : CC.Tm ε (A , B)) → F (G f) ∼ abs (snd · f)

  -- `ε` has no variables.
  FG (var ())

  -- G id = I, F I = abs snd; snd ∼ snd · id.
  FG id = ∼abs (∼sym (unitr snd))

  -- G fst = P₁, F P₁ = abs (snd · fst); on the nose.
  FG fst = ∼refl

  -- G snd = P₂, F P₂ = abs (snd · snd); on the nose.
  FG snd = ∼refl

  -- The computational base cases (`term`, `app`) and the inductive cases
  -- (`_·_`, `pair`, `abs`) name composites/products/curries of morphisms.  Each
  -- reduces `F (G f)` with the CC β-lemmas (`beta`/`ap·`/…) and, for the
  -- inductive ones, the induction hypotheses `FG …`, to `abs (snd · f)`.  These
  -- mirror the `F∼ lam*` reductions and are left open (long).
  -- G term = K T; one funext, `kβ`, then both maps into 𝟙 collapse by `text`.
  FG term = funext (∼trans redL (∼sym (aβ (snd · term))))
    where
      redL : ap (fst · F (K $ T)) snd ∼ (snd · term)
      redL = begin∼
        ap (fst · ap (F K) term) snd
          ∼⟨ ∼· (∼pair (ap· fst (F K) term) ∼refl) ∼refl ⟩
        ap (ap (fst · F K) (fst · term)) snd
          ∼⟨ kβ fst (fst · term) snd ⟩
        fst · term
          ∼⟨ ∼trans (text (fst · term)) (∼sym (text (snd · term))) ⟩
        snd · term ∎∼

  -- The inductive cases.  `G` sends composition/pairing/abstraction to S/K/P
  -- towers, so `F (G _)` is a nest of `ap`s over `F S`/`F K`/`F P`; one funext
  -- (or two for `abs`, whose result is an arrow) plus `sβ`/`kβ`/`pβ` reduce it,
  -- and the induction hypotheses `FG f`/`FG g` replace the sub-names.  Same shape
  -- as `app`/`term` above but longer; left open.
  FG (f · g) = {!!}
  FG (pair f g) = {!!}
  FG (abs f) = {!!}

  -- G app = S P₁ P₂; one funext, then the S/P₁/P₂ laws, and `snd` is its own
  -- pairing (pext).
  FG {A = A0} app = funext (∼trans redL (∼sym (aβ (snd · app))))
    where
      redL : ap (fst · F (S $ P₁ $ P₂)) snd ∼ (snd · app)
      redL = begin∼
        ap (fst · ap (ap (F S) (F P₁)) (F P₂)) snd
          ∼⟨ ∼· (∼pair (ap· fst (ap (F S) (F P₁)) (F P₂)) ∼refl) ∼refl ⟩
        ap (ap (fst · ap (F S) (F P₁)) (fst · F P₂)) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (ap· fst (F S) (F P₁)) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (fst · F P₁)) (fst · F P₂)) snd
          ∼⟨ sβ fst (fst · F P₁) (fst · F P₂) snd ⟩
        ap (ap (fst · F P₁) snd) (ap (fst · F P₂) snd)
          ∼⟨ ∼· (∼pair (p₁β fst snd) (p₂β fst snd)) ∼refl ⟩
        pair (snd · fst) (snd · snd) · app
          ∼⟨ ∼· (∼sym (pext snd)) ∼refl ⟩
        snd · app ∎∼
