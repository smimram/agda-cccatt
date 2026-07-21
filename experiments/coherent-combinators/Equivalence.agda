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

  -- Congruence for `ap`.  The reductions below rewrite deep inside spines of
  -- applications, and `∼ap` is what keeps that bearable: a rewrite `k` levels
  -- down is `∼ap (∼ap … (∼ap k ∼refl) …) ∼refl`.
  ∼ap : {X A B : Ty n} {f f' : Tm Γ (X , A ⇒ B)} {a a' : Tm Γ (X , A)} →
        f ∼ f' → a ∼ a' → ap f a ∼ ap f' a'
  ∼ap p q = ∼· (∼pair p q) ∼refl

  --- Extensionality in the form the closed `lam*` equations need.
  --
  -- Both sides of a `lam*` rule are global elements of an iterated exponential,
  -- so they can only be compared after being applied to as many generic
  -- arguments as the type has arrows.  Peeling one arrow off with `funext`
  -- introduces a projection in front of the term, which is why the statement has
  -- to be *generalized over an environment* `e`: the projection is then absorbed
  -- into `e` and the statement one arrow deeper applies verbatim.
  --
  -- `pushₖ` does that absorption for a spine of `k` applications, and `extₖ`
  -- turns a statement about `k` arguments into one about `k-1`; `ext0` finally
  -- instantiates the environment at the identity.

  push1 : {W Y X A B : Ty n} (e' : Tm Γ (W , Y)) (e : Tm Γ (Y , X))
          (h : Tm Γ (X , A ⇒ B)) (p : Tm Γ (Y , A)) →
          e' · ap (e · h) p ∼ ap ((e' · e) · h) (e' · p)
  push1 e' e h p = ∼trans (ap· e' (e · h) p) (∼ap (∼sym (assoc e' e h)) ∼refl)

  push2 : {W Y X A B C : Ty n} (e' : Tm Γ (W , Y)) (e : Tm Γ (Y , X))
          (h : Tm Γ (X , A ⇒ B ⇒ C)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B)) →
          e' · ap (ap (e · h) p) q ∼ ap (ap ((e' · e) · h) (e' · p)) (e' · q)
  push2 e' e h p q = ∼trans (ap· e' (ap (e · h) p) q) (∼ap (push1 e' e h p) ∼refl)

  push3 : {W Y X A B C D : Ty n} (e' : Tm Γ (W , Y)) (e : Tm Γ (Y , X))
          (h : Tm Γ (X , A ⇒ B ⇒ C ⇒ D)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B)) (r : Tm Γ (Y , C)) →
          e' · ap (ap (ap (e · h) p) q) r
          ∼ ap (ap (ap ((e' · e) · h) (e' · p)) (e' · q)) (e' · r)
  push3 e' e h p q r = ∼trans (ap· e' (ap (ap (e · h) p) q) r) (∼ap (push2 e' e h p q) ∼refl)

  ext0 : {X A : Ty n} {h h' : Tm Γ (X , A)} →
         ({Y : Ty n} (e : Tm Γ (Y , X)) → e · h ∼ e · h') → h ∼ h'
  ext0 {h = h} {h' = h'} hyp = ∼trans (∼sym (unitl h)) (∼trans (hyp id) (unitl h'))

  ext1 : {X A B : Ty n} {h h' : Tm Γ (X , A ⇒ B)} →
         ({Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) → ap (e · h) p ∼ ap (e · h') p) →
         {Y : Ty n} (e : Tm Γ (Y , X)) → e · h ∼ e · h'
  ext1 {h = h} {h' = h'} hyp e = funext
    (∼trans (∼ap (∼sym (assoc fst e h)) ∼refl)
      (∼trans (hyp (fst · e) snd) (∼ap (assoc fst e h') ∼refl)))

  ext2 : {X A B C : Ty n} {h h' : Tm Γ (X , A ⇒ B ⇒ C)} →
         ({Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B)) →
            ap (ap (e · h) p) q ∼ ap (ap (e · h') p) q) →
         {Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) → ap (e · h) p ∼ ap (e · h') p
  ext2 {h = h} {h' = h'} hyp e p = funext
    (∼trans (∼ap (push1 fst e h p) ∼refl)
      (∼trans (hyp (fst · e) (fst · p) snd) (∼ap (∼sym (push1 fst e h' p)) ∼refl)))

  ext3 : {X A B C D : Ty n} {h h' : Tm Γ (X , A ⇒ B ⇒ C ⇒ D)} →
         ({Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B)) (r : Tm Γ (Y , C)) →
            ap (ap (ap (e · h) p) q) r ∼ ap (ap (ap (e · h') p) q) r) →
         {Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B)) →
            ap (ap (e · h) p) q ∼ ap (ap (e · h') p) q
  ext3 {h = h} {h' = h'} hyp e p q = funext
    (∼trans (∼ap (push2 fst e h p q) ∼refl)
      (∼trans (hyp (fst · e) (fst · p) (fst · q) snd)
              (∼ap (∼sym (push2 fst e h' p q)) ∼refl)))

  ext4 : {X A B C D E : Ty n} {h h' : Tm Γ (X , A ⇒ B ⇒ C ⇒ D ⇒ E)} →
         ({Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B))
            (r : Tm Γ (Y , C)) (s : Tm Γ (Y , D)) →
            ap (ap (ap (ap (e · h) p) q) r) s ∼ ap (ap (ap (ap (e · h') p) q) r) s) →
         {Y : Ty n} (e : Tm Γ (Y , X)) (p : Tm Γ (Y , A)) (q : Tm Γ (Y , B)) (r : Tm Γ (Y , C)) →
            ap (ap (ap (e · h) p) q) r ∼ ap (ap (ap (e · h') p) q) r
  ext4 {h = h} {h' = h'} hyp e p q r = funext
    (∼trans (∼ap (push3 fst e h p q r) ∼refl)
      (∼trans (hyp (fst · e) (fst · p) (fst · q) (fst · r) snd)
              (∼ap (∼sym (push3 fst e h' p q r)) ∼refl)))

  -- The `F`-images of the CL combinators, spelled out as CC terms at an
  -- arbitrary context: `F I`, `F K`, … unfold to exactly these, so the laws and
  -- reductions stated with them apply to the `F`-images on the nose.
  fI : {A : Ty n} → Tm Γ (𝟙 , A ⇒ A)
  fI = abs snd

  fK : {A B : Ty n} → Tm Γ (𝟙 , A ⇒ B ⇒ A)
  fK = abs (abs (fst · snd))

  fS : {A B C : Ty n} → Tm Γ (𝟙 , (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  fS = abs (abs (abs (pair (pair (fst · fst · snd) snd · app)
                           (pair (fst · snd) snd · app) · app)))

  fP₁ : {A B : Ty n} → Tm Γ (𝟙 , A × B ⇒ A)
  fP₁ = abs (snd · fst)

  fP₂ : {A B : Ty n} → Tm Γ (𝟙 , A × B ⇒ B)
  fP₂ = abs (snd · snd)

  fP : {A B : Ty n} → Tm Γ (𝟙 , A ⇒ B ⇒ A × B)
  fP = abs (abs (pair (fst · snd) snd))

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

  --- Reduction of the closed `lam*` towers.
  --
  -- Each `lam*` rule of CL is an equation between two closed S/K towers; under
  -- `F` both sides become global elements of an iterated exponential.  The
  -- lemmas below compute what a side becomes once it sits under an environment
  -- `e` and is applied to as many generic arguments as its type has arrows;
  -- `F∼` then glues the two computations together with `ext0`/`ext1`/… .
  --
  -- Every step is one of exactly two moves: `ap·`, which distributes `e` over an
  -- application node of the tower, or one of `iβ`/`kβ`/`sβ`/`pβ`/`p₁β`/`p₂β`,
  -- which fires a combinator once all its arguments are present.

  -- lamKβ : S (K S) (S (K K)) ∼ K,  at (A ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C.
  fLKβ : {A B C : Ty n} → Tm Γ (𝟙 , (A ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  fLKβ = ap (ap fS (ap fK fS)) (ap fS (ap fK fK))

  redKβ : {X A B C : Ty n} (e : Tm Γ (X , 𝟙))
          (p : Tm Γ (X , A ⇒ C)) (q : Tm Γ (X , A ⇒ B)) (r : Tm Γ (X , A)) →
          ap (ap (ap (e · fLKβ) p) q) r ∼ ap p r
  redKβ e p q r = begin∼
    ap (ap (ap (e · ap (ap fS (ap fK fS)) (ap fS (ap fK fK))) p) q) r
      ∼⟨ ∼ap (∼ap (∼ap (ap· e (ap fS (ap fK fS)) (ap fS (ap fK fK))) ∼refl) ∼refl) ∼refl ⟩
    ap (ap (ap (ap (e · ap fS (ap fK fS)) (e · ap fS (ap fK fK))) p) q) r
      ∼⟨ ∼ap (∼ap (∼ap (∼ap (ap· e fS (ap fK fS)) (ap· e fS (ap fK fK))) ∼refl) ∼refl) ∼refl ⟩
    ap (ap (ap (ap (ap (e · fS) (e · ap fK fS)) (ap (e · fS) (e · ap fK fK))) p) q) r
      ∼⟨ ∼ap (∼ap (∼ap (∼ap (∼ap ∼refl (ap· e fK fS)) (∼ap ∼refl (ap· e fK fK))) ∼refl) ∼refl) ∼refl ⟩
    ap (ap (ap (ap (ap (e · fS) (ap (e · fK) (e · fS)))
                   (ap (e · fS) (ap (e · fK) (e · fK)))) p) q) r
      ∼⟨ ∼ap (∼ap (sβ e (ap (e · fK) (e · fS)) (ap (e · fS) (ap (e · fK) (e · fK))) p) ∼refl) ∼refl ⟩
    ap (ap (ap (ap (ap (e · fK) (e · fS)) p)
                   (ap (ap (e · fS) (ap (e · fK) (e · fK))) p)) q) r
      ∼⟨ ∼ap (∼ap (∼ap (kβ e (e · fS) p) ∼refl) ∼refl) ∼refl ⟩
    ap (ap (ap (e · fS) (ap (ap (e · fS) (ap (e · fK) (e · fK))) p)) q) r
      ∼⟨ sβ e (ap (ap (e · fS) (ap (e · fK) (e · fK))) p) q r ⟩
    ap (ap (ap (ap (e · fS) (ap (e · fK) (e · fK))) p) r) (ap q r)
      ∼⟨ ∼ap (sβ e (ap (e · fK) (e · fK)) p r) ∼refl ⟩
    ap (ap (ap (ap (e · fK) (e · fK)) r) (ap p r)) (ap q r)
      ∼⟨ ∼ap (∼ap (kβ e (e · fK) r) ∼refl) ∼refl ⟩
    ap (ap (e · fK) (ap p r)) (ap q r)
      ∼⟨ kβ e (ap p r) (ap q r) ⟩
    ap p r ∎∼

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
  F∼ CL.lamKβ =
    ext0 (ext1 (ext2 (ext3 (λ e p q r →
      CC.∼trans (redKβ e p q r) (CC.∼sym (∼ap (kβ e p q) CC.∼refl))))))
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
  -- `F K = abs (abs (fst · snd))`, so `G (F K)` is two `abs`-layers
  -- `S (K (S (K -))) P` around `G (fst · snd) = S (K P₂) P₁`.  Applying it to `T`
  -- and then (under two `funext`s) to `x0 x1` builds the environment
  -- `w1 = P (P T x0) x1` and reads the second component of its first component.
  GF (K {A = A} {B = B}) = ∼trans redK (CL.funext (CL.funext (∼trans redz (∼sym (Kβ x0 x1)))))
    where
      x0 : Tm (ε' {n} ▹' A ▹' B) A
      x0 = var (drop' here')

      x1 : Tm (ε' {n} ▹' A ▹' B) B
      x1 = var here'

      w0 : Tm (ε' {n} ▹' A ▹' B) (𝟙 × A)
      w0 = P $ T $ x0

      w1 : Tm (ε' {n} ▹' A ▹' B) ((𝟙 × A) × B)
      w1 = P $ w0 $ x1

      -- The body of the inner abstraction, in the extended context.
      m : Tm (ε' {n} ▹' A ▹' B) ((𝟙 × A) × B ⇒ A)
      m = S $ (K $ P₂) $ P₁

      redK : (G (F (K {A = A} {B = B})) $ T)
             ∼ (S $ (K $ (S $ (K $ (S $ (K $ (S $ (K $ P₂) $ P₁)))) $ P)) $ (P $ T))
      redK = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

      redz : (S $ (K $ (S $ (K $ (S $ (K $ (S $ (K $ P₂) $ P₁)))) $ P)) $ (P $ T) $ x0 $ x1) ∼ x0
      redz =
        ∼trans (∼$ (comp$ (S $ (K $ (S $ (K $ m))) $ P) (P $ T) x0) ∼refl)
          (∼trans (∼$ (abs$ m w0) ∼refl)
            (∼trans (comp$ m (P $ w0) x1)
              (∼trans (comp$ P₂ P₁ w1)
                (∼trans (∼$ ∼refl (P₁β w0 x1)) (P₂β T x0)))))

  -- `F P = abs (abs (pair (fst · snd) snd))`: same two `abs`-layers as `K`, but
  -- the body is a pairing, so `pair$` splits it and the two halves are read off
  -- the environment `w1 = P (P T x0) x1`.
  GF (P {A = A} {B = B}) = ∼trans redP (CL.funext (CL.funext redz))
    where
      x0 : Tm (ε' {n} ▹' A ▹' B) A
      x0 = var (drop' here')

      x1 : Tm (ε' {n} ▹' A ▹' B) B
      x1 = var here'

      w0 : Tm (ε' {n} ▹' A ▹' B) (𝟙 × A)
      w0 = P $ T $ x0

      w1 : Tm (ε' {n} ▹' A ▹' B) ((𝟙 × A) × B)
      w1 = P $ w0 $ x1

      -- `G (fst · snd)` and `G (pair (fst · snd) snd)`, at any context.
      mfs : {Δ : Con' n} → Tm Δ ((𝟙 × A) × B ⇒ A)
      mfs = S $ (K $ P₂) $ P₁

      mp : {Δ : Con' n} → Tm Δ ((𝟙 × A) × B ⇒ A × B)
      mp = S $ (S $ (K $ P) $ mfs) $ P₂

      inner : {Δ : Con' n} → Tm Δ (𝟙 × A ⇒ B ⇒ A × B)
      inner = S $ (K $ (S $ (K $ mp))) $ P

      redP : (G (F (P {A = A} {B = B})) $ T) ∼ (S $ (K $ inner) $ (P $ T))
      redP = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

      -- `S (K P₂) P₁` applied to the environment picks out `x0`.
      redfs : (mfs $ w1) ∼ x0
      redfs = ∼trans (comp$ P₂ P₁ w1) (∼trans (∼$ ∼refl (P₁β w0 x1)) (P₂β T x0))

      redz : (S $ (K $ inner) $ (P $ T) $ x0 $ x1) ∼ (P $ x0 $ x1)
      redz =
        ∼trans (∼$ (comp$ inner (P $ T) x0) ∼refl)
          (∼trans (∼$ (abs$ mp w0) ∼refl)
            (∼trans (comp$ mp (P $ w0) x1)
              (∼trans (pair$ mfs P₂ w1)
                      (∼$ (∼$ ∼refl redfs) (P₂β w0 x1)))))

  -- `F S = abs (abs (abs BODY))`: three `abs`-layers, and `BODY` is a tree of two
  -- CC applications, so `G BODY` is a nest of `S (K (S P₁ P₂)) -` (the image of
  -- `app`) over pairings.  Under three `funext`s everything reduces against the
  -- environment `w2 = P (P (P T x0) x1) x2`.
  GF (S {A = A} {B = B} {C = C}) =
    ∼trans redS (CL.funext (CL.funext (CL.funext (∼trans redz (∼sym (Sβ x0 x1 x2))))))
    where
      Δ : Con' n
      Δ = ε' ▹' (A ⇒ B ⇒ C) ▹' (A ⇒ B) ▹' A

      x0 : Tm Δ (A ⇒ B ⇒ C)
      x0 = var (drop' (drop' here'))

      x1 : Tm Δ (A ⇒ B)
      x1 = var (drop' here')

      x2 : Tm Δ A
      x2 = var here'

      w0 : Tm Δ (𝟙 × (A ⇒ B ⇒ C))
      w0 = P $ T $ x0

      w1 : Tm Δ ((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B))
      w1 = P $ w0 $ x1

      w2 : Tm Δ (((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A)
      w2 = P $ w1 $ x2

      -- `G app`, at whichever exponential it is used.
      gapp : {Δ' : Con' n} {U V : Ty n} → Tm Δ' ((U ⇒ V) × U ⇒ V)
      gapp = S $ P₁ $ P₂

      -- `G (fst · fst · snd)` and `G (fst · snd)`: the two projections of the
      -- environment that `BODY` reads.
      gffs : {Δ' : Con' n} → Tm Δ' (((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A ⇒ A ⇒ B ⇒ C)
      gffs = S $ (K $ P₂) $ (S $ (K $ P₁) $ P₁)

      gfs : {Δ' : Con' n} → Tm Δ' (((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A ⇒ A ⇒ B)
      gfs = S $ (K $ P₂) $ P₁

      -- The two operands of the outer application in `BODY`, then `BODY` itself.
      gU : {Δ' : Con' n} → Tm Δ' (((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A ⇒ B ⇒ C)
      gU = S $ (K $ gapp) $ (S $ (S $ (K $ P) $ gffs) $ P₂)

      gV : {Δ' : Con' n} → Tm Δ' (((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A ⇒ B)
      gV = S $ (K $ gapp) $ (S $ (S $ (K $ P) $ gfs) $ P₂)

      gBODY : {Δ' : Con' n} → Tm Δ' (((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B)) × A ⇒ C)
      gBODY = S $ (K $ gapp) $ (S $ (S $ (K $ P) $ gU) $ gV)

      -- The three `abs`-layers.
      tw1 : {Δ' : Con' n} → Tm Δ' ((𝟙 × (A ⇒ B ⇒ C)) × (A ⇒ B) ⇒ A ⇒ C)
      tw1 = S $ (K $ (S $ (K $ gBODY))) $ P

      tw2 : {Δ' : Con' n} → Tm Δ' (𝟙 × (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
      tw2 = S $ (K $ (S $ (K $ tw1))) $ P

      redS : (G (F (S {A = A} {B = B} {C = C})) $ T) ∼ (S $ (K $ tw2) $ (P $ T))
      redS = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

      redffs : (gffs $ w2) ∼ x0
      redffs =
        ∼trans (comp$ P₂ (S $ (K $ P₁) $ P₁) w2)
          (∼trans (∼$ ∼refl (comp$ P₁ P₁ w2))
            (∼trans (∼$ ∼refl (∼$ ∼refl (P₁β w1 x2)))
              (∼trans (∼$ ∼refl (P₁β w0 x1)) (P₂β T x0))))

      redfs : (gfs $ w2) ∼ x1
      redfs = ∼trans (comp$ P₂ P₁ w2)
                (∼trans (∼$ ∼refl (P₁β w1 x2)) (P₂β w0 x1))

      -- Both operands are "apply the projection to `x2`": same reduction twice.
      redU : (gU $ w2) ∼ (x0 $ x2)
      redU =
        ∼trans (comp$ gapp (S $ (S $ (K $ P) $ gffs) $ P₂) w2)
          (∼trans (∼$ ∼refl (pair$ gffs P₂ w2))
            (∼trans (∼$ ∼refl (∼$ (∼$ ∼refl redffs) (P₂β w1 x2)))
              (∼trans (app$ (P $ x0 $ x2)) (∼$ (P₁β x0 x2) (P₂β x0 x2)))))

      redV : (gV $ w2) ∼ (x1 $ x2)
      redV =
        ∼trans (comp$ gapp (S $ (S $ (K $ P) $ gfs) $ P₂) w2)
          (∼trans (∼$ ∼refl (pair$ gfs P₂ w2))
            (∼trans (∼$ ∼refl (∼$ (∼$ ∼refl redfs) (P₂β w1 x2)))
              (∼trans (app$ (P $ x1 $ x2)) (∼$ (P₁β x1 x2) (P₂β x1 x2)))))

      redz : (S $ (K $ tw2) $ (P $ T) $ x0 $ x1 $ x2) ∼ ((x0 $ x2) $ (x1 $ x2))
      redz =
        ∼trans (∼$ (∼$ (comp$ tw2 (P $ T) x0) ∼refl) ∼refl)
          (∼trans (∼$ (∼$ (abs$ tw1 w0) ∼refl) ∼refl)
            (∼trans (∼$ (comp$ tw1 (P $ w0) x1) ∼refl)
              (∼trans (∼$ (abs$ gBODY w1) ∼refl)
                (∼trans (comp$ gBODY (P $ w1) x2)
                  (∼trans (comp$ gapp (S $ (S $ (K $ P) $ gU) $ gV) w2)
                    (∼trans (∼$ ∼refl (pair$ gU gV w2))
                      (∼trans (∼$ ∼refl (∼$ (∼$ ∼refl redU) redV))
                        (∼trans (app$ (P $ (x0 $ x2) $ (x1 $ x2)))
                                (∼$ (P₁β _ _) (P₂β _ _))))))))))

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
  -- G (f · g) = S (K (G g)) (G f).  One funext; `sβ`/`kβ` collapse the tower to
  -- `ap (fst · F (G g)) (ap (fst · F (G f)) snd)`, the induction hypotheses turn
  -- the two names into `abs (snd · f)` / `abs (snd · g)`, and `aβ`/`beta` peel
  -- them off, leaving `snd · f · g`.
  FG (f · g) = funext (∼trans redL (∼sym (aβ (snd · (f · g)))))
    where
      redL : ap (fst · F (G (f · g))) snd ∼ (snd · (f · g))
      redL = begin∼
        ap (fst · ap (ap (F S) (ap (F K) (F (G g)))) (F (G f))) snd
          ∼⟨ ∼· (∼pair (ap· fst (ap (F S) (ap (F K) (F (G g)))) (F (G f))) ∼refl) ∼refl ⟩
        ap (ap (fst · ap (F S) (ap (F K) (F (G g)))) (fst · F (G f))) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (ap· fst (F S) (ap (F K) (F (G g)))) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (fst · ap (F K) (F (G g)))) (fst · F (G f))) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (∼· (∼pair ∼refl (ap· fst (F K) (F (G g)))) ∼refl) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (ap (fst · F K) (fst · F (G g)))) (fst · F (G f))) snd
          ∼⟨ sβ fst (ap (fst · F K) (fst · F (G g))) (fst · F (G f)) snd ⟩
        ap (ap (ap (fst · F K) (fst · F (G g))) snd) (ap (fst · F (G f)) snd)
          ∼⟨ ∼· (∼pair (kβ fst (fst · F (G g)) snd) ∼refl) ∼refl ⟩
        ap (fst · F (G g)) (ap (fst · F (G f)) snd)
          ∼⟨ ∼· (∼pair (∼· ∼refl (FG g)) (∼· (∼pair (∼· ∼refl (FG f)) ∼refl) ∼refl)) ∼refl ⟩
        ap (fst · abs (snd · g)) (ap (fst · abs (snd · f)) snd)
          ∼⟨ ∼· (∼pair ∼refl (aβ (snd · f))) ∼refl ⟩
        ap (fst · abs (snd · g)) (snd · f)
          ∼⟨ beta (snd · g) fst (snd · f) ⟩
        pair fst (snd · f) · (snd · g)
          ∼⟨ ∼sym (assoc _ _ _) ⟩
        pair fst (snd · f) · snd · g
          ∼⟨ ∼· (psnd fst (snd · f)) ∼refl ⟩
        snd · f · g
          ∼⟨ assoc snd f g ⟩
        snd · (f · g) ∎∼

  -- G (pair f g) = S (S (K P) (G f)) (G g): two nested S-towers over `F P`, so
  -- two `sβ`s and a `kβ` expose `pβ`, which rebuilds an actual `pair`.
  FG (pair f g) =
    funext (∼trans redL (∼sym (∼trans (aβ (snd · pair f g)) (pairComp snd f g))))
    where
      -- The inner tower `S (K P) (G f)`, with `fst` already pushed in.
      redQ : ap (ap (ap (fst · F S) (ap (fst · F K) (fst · F P))) (fst · F (G f))) snd
             ∼ ap (fst · F P) (ap (fst · F (G f)) snd)
      redQ = begin∼
        ap (ap (ap (fst · F S) (ap (fst · F K) (fst · F P))) (fst · F (G f))) snd
          ∼⟨ sβ fst (ap (fst · F K) (fst · F P)) (fst · F (G f)) snd ⟩
        ap (ap (ap (fst · F K) (fst · F P)) snd) (ap (fst · F (G f)) snd)
          ∼⟨ ∼· (∼pair (kβ fst (fst · F P) snd) ∼refl) ∼refl ⟩
        ap (fst · F P) (ap (fst · F (G f)) snd) ∎∼

      redL : ap (fst · F (G (pair f g))) snd ∼ pair (snd · f) (snd · g)
      redL = begin∼
        ap (fst · ap (ap (F S) (ap (ap (F S) (ap (F K) (F P))) (F (G f)))) (F (G g))) snd
          ∼⟨ ∼· (∼pair (ap· fst (ap (F S) (ap (ap (F S) (ap (F K) (F P))) (F (G f)))) (F (G g))) ∼refl) ∼refl ⟩
        ap (ap (fst · ap (F S) (ap (ap (F S) (ap (F K) (F P))) (F (G f)))) (fst · F (G g))) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (ap· fst (F S) (ap (ap (F S) (ap (F K) (F P))) (F (G f)))) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (fst · ap (ap (F S) (ap (F K) (F P))) (F (G f)))) (fst · F (G g))) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (∼· (∼pair ∼refl (ap· fst (ap (F S) (ap (F K) (F P))) (F (G f)))) ∼refl) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (ap (fst · ap (F S) (ap (F K) (F P))) (fst · F (G f)))) (fst · F (G g))) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (∼· (∼pair ∼refl (∼· (∼pair (ap· fst (F S) (ap (F K) (F P))) ∼refl) ∼refl)) ∼refl) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (ap (ap (fst · F S) (fst · ap (F K) (F P))) (fst · F (G f)))) (fst · F (G g))) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (∼· (∼pair ∼refl (∼· (∼pair (∼· (∼pair ∼refl (ap· fst (F K) (F P))) ∼refl) ∼refl) ∼refl)) ∼refl) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (ap (ap (fst · F S) (ap (fst · F K) (fst · F P))) (fst · F (G f)))) (fst · F (G g))) snd
          ∼⟨ sβ fst (ap (ap (fst · F S) (ap (fst · F K) (fst · F P))) (fst · F (G f))) (fst · F (G g)) snd ⟩
        ap (ap (ap (ap (fst · F S) (ap (fst · F K) (fst · F P))) (fst · F (G f))) snd) (ap (fst · F (G g)) snd)
          ∼⟨ ∼· (∼pair redQ ∼refl) ∼refl ⟩
        ap (ap (fst · F P) (ap (fst · F (G f)) snd)) (ap (fst · F (G g)) snd)
          ∼⟨ pβ fst (ap (fst · F (G f)) snd) (ap (fst · F (G g)) snd) ⟩
        pair (ap (fst · F (G f)) snd) (ap (fst · F (G g)) snd)
          ∼⟨ ∼pair (∼· (∼pair (∼· ∼refl (FG f)) ∼refl) ∼refl) (∼· (∼pair (∼· ∼refl (FG g)) ∼refl) ∼refl) ⟩
        pair (ap (fst · abs (snd · f)) snd) (ap (fst · abs (snd · g)) snd)
          ∼⟨ ∼pair (aβ (snd · f)) (aβ (snd · g)) ⟩
        pair (snd · f) (snd · g) ∎∼

  -- G (abs f) = S (K (S (K (G f)))) P.  The result is an arrow into an arrow, so
  -- two funexts: the first (over 𝟙 × A) peels the outer S/K layer down to `M1`,
  -- the second (over (𝟙 × A) × B) pushes the new projections into a single
  -- environment `e₂ = fst · fst` and lets `sβ`/`kβ`/`pβ` rebuild the pair
  -- `pair u snd` that `f` is applied to.  Both sides land on `pair u snd · f`.
  FG (abs {A = A} {B = B} {C = C} f) = funext (funext (∼trans redL (∼sym redR)))
    where
      -- The environment and the generic first argument, over Θ = (𝟙 × A) × B.
      e₂ : Tm ε ((𝟙 × A) × B , 𝟙)
      e₂ = fst · fst

      u : Tm ε ((𝟙 × A) × B , A)
      u = fst · snd

      -- `F (S $ (K $ G f))`, the inner S/K layer.
      FZ : Tm ε (𝟙 , (B ⇒ A × B) ⇒ B ⇒ C)
      FZ = ap (F S) (ap (F K) (F (G f)))

      -- What the first funext reduces the left-hand side to.
      M1 : Tm ε (𝟙 × A , B ⇒ C)
      M1 = ap (fst · FZ) (ap (fst · F P) snd)

      red1 : ap (fst · F (G (abs f))) snd ∼ M1
      red1 = begin∼
        ap (fst · ap (ap (F S) (ap (F K) FZ)) (F P)) snd
          ∼⟨ ∼· (∼pair (ap· fst (ap (F S) (ap (F K) FZ)) (F P)) ∼refl) ∼refl ⟩
        ap (ap (fst · ap (F S) (ap (F K) FZ)) (fst · F P)) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (ap· fst (F S) (ap (F K) FZ)) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (fst · ap (F K) FZ)) (fst · F P)) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair (∼· (∼pair ∼refl (ap· fst (F K) FZ)) ∼refl) ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (fst · F S) (ap (fst · F K) (fst · FZ))) (fst · F P)) snd
          ∼⟨ sβ fst (ap (fst · F K) (fst · FZ)) (fst · F P) snd ⟩
        ap (ap (ap (fst · F K) (fst · FZ)) snd) (ap (fst · F P) snd)
          ∼⟨ ∼· (∼pair (kβ fst (fst · FZ) snd) ∼refl) ∼refl ⟩
        ap (fst · FZ) (ap (fst · F P) snd) ∎∼

      -- The second funext's projections merge into the single environment `e₂`.
      red2 : (fst · M1) ∼ ap (e₂ · FZ) (ap (e₂ · F P) u)
      red2 = begin∼
        fst · ap (fst · FZ) (ap (fst · F P) snd)
          ∼⟨ ap· fst (fst · FZ) (ap (fst · F P) snd) ⟩
        ap (fst · (fst · FZ)) (fst · ap (fst · F P) snd)
          ∼⟨ ∼· (∼pair (∼sym (assoc fst fst FZ)) (ap· fst (fst · F P) snd)) ∼refl ⟩
        ap (e₂ · FZ) (ap (fst · (fst · F P)) (fst · snd))
          ∼⟨ ∼· (∼pair ∼refl (∼· (∼pair (∼sym (assoc fst fst (F P))) ∼refl) ∼refl)) ∼refl ⟩
        ap (e₂ · FZ) (ap (e₂ · F P) u) ∎∼

      redFZ : (e₂ · FZ) ∼ ap (e₂ · F S) (ap (e₂ · F K) (e₂ · F (G f)))
      redFZ = ∼trans (ap· e₂ (F S) (ap (F K) (F (G f))))
                     (∼· (∼pair ∼refl (ap· e₂ (F K) (F (G f)))) ∼refl)

      redL : ap (fst · ap (fst · F (G (abs f))) snd) snd ∼ (pair u snd · f)
      redL = begin∼
        ap (fst · ap (fst · F (G (abs f))) snd) snd
          ∼⟨ ∼· (∼pair (∼· ∼refl red1) ∼refl) ∼refl ⟩
        ap (fst · M1) snd
          ∼⟨ ∼· (∼pair red2 ∼refl) ∼refl ⟩
        ap (ap (e₂ · FZ) (ap (e₂ · F P) u)) snd
          ∼⟨ ∼· (∼pair (∼· (∼pair redFZ ∼refl) ∼refl) ∼refl) ∼refl ⟩
        ap (ap (ap (e₂ · F S) (ap (e₂ · F K) (e₂ · F (G f)))) (ap (e₂ · F P) u)) snd
          ∼⟨ sβ e₂ (ap (e₂ · F K) (e₂ · F (G f))) (ap (e₂ · F P) u) snd ⟩
        ap (ap (ap (e₂ · F K) (e₂ · F (G f))) snd) (ap (ap (e₂ · F P) u) snd)
          ∼⟨ ∼· (∼pair (kβ e₂ (e₂ · F (G f)) snd) (pβ e₂ u snd)) ∼refl ⟩
        ap (e₂ · F (G f)) (pair u snd)
          ∼⟨ ∼· (∼pair (∼· ∼refl (FG f)) ∼refl) ∼refl ⟩
        ap (e₂ · abs (snd · f)) (pair u snd)
          ∼⟨ beta (snd · f) e₂ (pair u snd) ⟩
        pair e₂ (pair u snd) · (snd · f)
          ∼⟨ ∼sym (assoc _ _ _) ⟩
        pair e₂ (pair u snd) · snd · f
          ∼⟨ ∼· (psnd e₂ (pair u snd)) ∼refl ⟩
        pair u snd · f ∎∼

      redR : ap (fst · ap (fst · abs (snd · abs f)) snd) snd ∼ (pair u snd · f)
      redR = begin∼
        ap (fst · ap (fst · abs (snd · abs f)) snd) snd
          ∼⟨ ∼· (∼pair (∼· ∼refl (aβ (snd · abs f))) ∼refl) ∼refl ⟩
        ap (fst · (snd · abs f)) snd
          ∼⟨ ∼· (∼pair (∼sym (assoc fst snd (abs f))) ∼refl) ∼refl ⟩
        ap (u · abs f) snd
          ∼⟨ beta f u snd ⟩
        pair u snd · f ∎∼

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
