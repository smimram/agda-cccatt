--- Normalization by evaluation for cartesian closed categories
---
--- Every term with source 𝟙 is equivalent to a canonical (βη-long) one: we
--- construct the normal form (nf), show that it is canonical (nfCan) and that
--- it is equivalent to the original term (nf∼).

open import Prelude
open import Ty
open import PS
open import CC

--- Renamings
---
--- Weakening is not available on terms yet: we use plain functions on variables
--- (as PSTgtConTm already does with its incl argument) rather than the Sub
--- machinery, which would require SubTyId and thus SubTyUnitL (a hole in Ty).

Ren : {n : ℕ} → Con n → Con n → Type
Ren {n} Γ Δ = {A : Arr n} → A ∈ Γ → A ∈ Δ

idRen : {n : ℕ} {Γ : Con n} → Ren Γ Γ
idRen x = x

_∘R_ : {n : ℕ} {Γ Δ Θ : Con n} → Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘R ρ) x = ρ' (ρ x)

-- Extend the context by one variable
wkRen : {n : ℕ} {Γ : Con n} {A : Arr n} → Ren Γ (Γ ▹ A)
wkRen x = drop x

-- Transport a renaming under a binder
_⁺ : {n : ℕ} {Γ Δ : Con n} {A : Arr n} → Ren Γ Δ → Ren (Γ ▹ A) (Δ ▹ A)
(ρ ⁺) here = here
(ρ ⁺) (drop x) = drop (ρ x)

-- Action on terms
ren : {n : ℕ} {Γ Δ : Con n} {A : Arr n} → Ren Γ Δ → Tm Γ A → Tm Δ A
ren ρ (var x) = var (ρ x)
ren ρ id = id
ren ρ (f · g) = ren ρ f · ren ρ g
ren ρ term = term
ren ρ (pair f g) = pair (ren ρ f) (ren ρ g)
ren ρ fst = fst
ren ρ snd = snd
ren ρ (abs t) = abs (ren ρ t)
ren ρ app = app

--- Renaming preserves canonicity

-- Renaming commutes with binding the last variable
renClose : {n : ℕ} {Γ Δ : Con n} {A B C : Ty n} (ρ : Ren Γ Δ) (t : Tm (Γ ▹ (𝟙 , A)) (B , C)) → ren ρ (close t) ≡ close (ren (ρ ⁺) t)
renClose ρ (var here) = refl
renClose ρ (var (drop x)) = refl
renClose ρ id = refl
renClose ρ (f · g) = cong₂ (λ f g → pair f snd · g) (renClose ρ f) (renClose ρ g)
renClose ρ term = refl
renClose ρ (pair f g) = cong₂ pair (renClose ρ f) (renClose ρ g)
renClose ρ fst = refl
renClose ρ snd = refl
renClose ρ (abs t) = cong (λ t → abs (pair (pair (fst · fst) snd) (fst · snd) · t)) (renClose ρ t)
renClose ρ app = refl

renCan : {n : ℕ} {Γ Δ : Con n} {A : Ty n} {t : Tm Γ (𝟙 , A)} (ρ : Ren Γ Δ) → canonical t → canonical (ren ρ t)
renNeu : {n : ℕ} {Γ Δ : Con n} {A : Ty n} {t : Tm Γ (𝟙 , A)} (ρ : Ren Γ Δ) → neutral t → neutral (ren ρ t)

renCan ρ (can-pair ct cu) = can-pair (renCan ρ ct) (renCan ρ cu)
renCan ρ can-term = can-term
renCan ρ (can-abs {t = t} ct) = subst (λ u → canonical (abs u)) (sym (renClose ρ t)) (can-abs (renCan (ρ ⁺) ct))
renCan ρ (can-neu nt) = can-neu (renNeu ρ nt)

renNeu ρ (neu-var ct x) = neu-var (renCan ρ ct) (ρ x)
renNeu ρ (neu-app nt cu) = neu-app (renNeu ρ nt) (renCan ρ cu)
renNeu ρ (neu-fst nt) = neu-fst (renNeu ρ nt)
renNeu ρ (neu-snd nt) = neu-snd (renNeu ρ nt)

--- The semantic domain
---
--- Normal and neutral forms bundle the term with its canonicity witness, so
--- that reification produces the proof of nfCan along with the term.

Ne : {n : ℕ} (Γ : Con n) (A : Ty n) → Type
Ne Γ A = Σ (Tm Γ (𝟙 , A)) neutral

Nf : {n : ℕ} (Γ : Con n) (A : Ty n) → Type
Nf Γ A = Σ (Tm Γ (𝟙 , A)) canonical

-- Values: neutral terms at base types, and a Kripke function space at arrows
⟦_⟧ : {n : ℕ} → Ty n → Con n → Type
⟦ X x ⟧ Γ = Ne Γ (X x)
⟦ 𝟙 ⟧ Γ = Unit
⟦ A × B ⟧ Γ = ⟦ A ⟧ Γ ∧ ⟦ B ⟧ Γ
⟦ A ⇒ B ⟧ Γ = {Δ : Con _} → Ren Γ Δ → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ

⟦⟧wk : {n : ℕ} {Γ Δ : Con n} (A : Ty n) → Ren Γ Δ → ⟦ A ⟧ Γ → ⟦ A ⟧ Δ
⟦⟧wk (X x) ρ (t , nt) = ren ρ t , renNeu ρ nt
⟦⟧wk 𝟙 ρ a = tt
⟦⟧wk (A × B) ρ (a , b) = ⟦⟧wk A ρ a , ⟦⟧wk B ρ b
⟦⟧wk (A ⇒ B) ρ f = λ ρ' a → f (ρ' ∘R ρ) a

--- Reflection and reification, by induction on the type

reflect : {n : ℕ} {Γ : Con n} (A : Ty n) → Ne Γ A → ⟦ A ⟧ Γ
reify : {n : ℕ} {Γ : Con n} (A : Ty n) → ⟦ A ⟧ Γ → Nf Γ A

reflect (X x) t = t
reflect 𝟙 t = tt
reflect (A × B) (t , nt) = reflect A (t · fst , neu-fst nt) , reflect B (t · snd , neu-snd nt)
reflect (A ⇒ B) (t , nt) = λ ρ a →
  let (u , cu) = reify A a in
  reflect B (pair (ren ρ t) u · app , neu-app (renNeu ρ nt) cu)

reify (X x) (t , nt) = t , can-neu nt
reify 𝟙 a = term , can-term
reify (A × B) (a , b) =
  let (t , ct) = reify A a in
  let (u , cu) = reify B b in
  pair t u , can-pair ct cu
-- The fresh variable of the extended context is used as the neutral term · var
-- here, and close turns the body back into a morphism 𝟙 × A → B
reify (A ⇒ B) f =
  let (t , ct) = reify B (f wkRen (reflect A (term · var here , neu-var can-term here))) in
  abs (close t) , can-abs ct

--- Evaluation
---
--- Indexed by a renaming, so that the abs case does not have to rename the
--- term it recurses on (which would break structural recursion).

eval : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → {Δ : Con n} → Ren Γ Δ → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ
eval {A = A} {B} (var x) ρ a =
  let (t , ct) = reify A a in
  reflect B (t · var (ρ x) , neu-var ct (ρ x))
eval id ρ a = a
eval (f · g) ρ a = eval g ρ (eval f ρ a)
eval term ρ a = tt
eval (pair f g) ρ a = eval f ρ a , eval g ρ a
eval fst ρ (a , b) = a
eval snd ρ (a , b) = b
eval (abs f) ρ a = λ ρ' b → eval f (ρ' ∘R ρ) (⟦⟧wk _ ρ' a , b)
eval app ρ (f , a) = f idRen a

--- Normal forms

nf' : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (𝟙 , A) → Nf Γ A
nf' {A = A} t = reify A (eval t idRen tt)

nf : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (𝟙 , A) → Tm Γ (𝟙 , A)
nf t = proj₁ (nf' t)

nfCan : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → canonical (nf t)
nfCan t = proj₂ (nf' t)

--- Soundness: the normal form is equivalent to the original term

-- Renamings act functorially

renId : {n : ℕ} {Γ : Con n} {A : Arr n} (t : Tm Γ A) → ren idRen t ≡ t
renId (var x) = refl
renId id = refl
renId (f · g) = cong₂ _·_ (renId f) (renId g)
renId term = refl
renId (pair f g) = cong₂ pair (renId f) (renId g)
renId fst = refl
renId snd = refl
renId (abs t) = cong abs (renId t)
renId app = refl

renComp : {n : ℕ} {Γ Δ Θ : Con n} {A : Arr n} (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) (t : Tm Γ A) → ren ρ' (ren ρ t) ≡ ren (ρ' ∘R ρ) t
renComp ρ' ρ (var x) = refl
renComp ρ' ρ id = refl
renComp ρ' ρ (f · g) = cong₂ _·_ (renComp ρ' ρ f) (renComp ρ' ρ g)
renComp ρ' ρ term = refl
renComp ρ' ρ (pair f g) = cong₂ pair (renComp ρ' ρ f) (renComp ρ' ρ g)
renComp ρ' ρ fst = refl
renComp ρ' ρ snd = refl
renComp ρ' ρ (abs t) = cong abs (renComp ρ' ρ t)
renComp ρ' ρ app = refl

-- Renaming preserves the equivalence: ren is a homomorphism, so every case is
-- the corresponding constructor
ren∼ : {n : ℕ} {Γ Δ : Con n} {A : Arr n} {t u : Tm Γ A} (ρ : Ren Γ Δ) → t ∼ u → ren ρ t ∼ ren ρ u
ren∼ ρ (pfst f g) = pfst (ren ρ f) (ren ρ g)
ren∼ ρ (psnd f g) = psnd (ren ρ f) (ren ρ g)
ren∼ ρ (pext f) = pext (ren ρ f)
ren∼ ρ (text f) = text (ren ρ f)
ren∼ ρ (aβ f) = aβ (ren ρ f)
ren∼ ρ (aext f) = aext (ren ρ f)
ren∼ ρ (unitl f) = unitl (ren ρ f)
ren∼ ρ (unitr f) = unitr (ren ρ f)
ren∼ ρ (assoc f g h) = assoc (ren ρ f) (ren ρ g) (ren ρ h)
ren∼ ρ (∼· p q) = ∼· (ren∼ ρ p) (ren∼ ρ q)
ren∼ ρ (∼pair p q) = ∼pair (ren∼ ρ p) (ren∼ ρ q)
ren∼ ρ (∼abs p) = ∼abs (ren∼ ρ p)
ren∼ ρ ∼refl = ∼refl
ren∼ ρ (∼sym p) = ∼sym (ren∼ ρ p)
ren∼ ρ (∼trans p q) = ∼trans (ren∼ ρ p) (ren∼ ρ q)

--- Elementary consequences of the cartesian closed structure

-- Composition distributes over pairing
pairComp : {n : ℕ} {Γ : Con n} {E X A B : Ty n} (h : Tm Γ (E , X)) (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → h · pair f g ∼ pair (h · f) (h · g)
pairComp h f g = ∼trans (pext (h · pair f g)) (∼pair
  (∼trans (assoc h (pair f g) fst) (∼· ∼refl (pfst f g)))
  (∼trans (assoc h (pair f g) snd) (∼· ∼refl (psnd f g))))

-- The pairing of the projections is the identity
pairId : {n : ℕ} {Γ : Con n} {A B : Ty n} → pair {Γ = Γ} {X = A × B} fst snd ∼ id
pairId = ∼sym (∼trans (pext id) (∼pair (unitl fst) (unitl snd)))

-- Naturality of currying
absComp : {n : ℕ} {Γ : Con n} {E A B C : Ty n} (h : Tm Γ (E , A)) (g : Tm Γ (A × B , C)) → h · abs g ∼ abs (pair (fst · h) snd · g)
absComp h g = ∼trans (aext (h · abs g)) (∼abs (∼trans
  (∼· (∼pair (∼trans (∼sym (assoc fst h (abs g)))
                     (∼trans (∼· (∼sym (pfst (fst · h) snd)) ∼refl) (assoc (pair (fst · h) snd) fst (abs g))))
             (∼sym (psnd (fst · h) snd)))
      ∼refl)
  (∼trans (∼· (∼sym (pairComp (pair (fst · h) snd) (fst · abs g) snd)) ∼refl)
          (∼trans (assoc (pair (fst · h) snd) (pair (fst · abs g) snd) app) (∼· ∼refl (aβ g))))))

-- β in pointed form: applying an abstraction to a point
absβ : {n : ℕ} {Γ : Con n} {A B C : Ty n} (u : Tm Γ (𝟙 , A)) (w : Tm Γ (𝟙 , B)) (g : Tm Γ (A × B , C)) → pair (u · abs g) w · app ∼ pair u w · g
absβ u w g = ∼trans
  (∼· (∼pair (∼trans (∼· (∼sym (pfst u w)) ∼refl) (assoc (pair u w) fst (abs g)))
             (∼sym (psnd u w)))
      ∼refl)
  (∼trans (∼· (∼sym (pairComp (pair u w) (fst · abs g) snd)) ∼refl)
          (∼trans (assoc (pair u w) (pair (fst · abs g) snd) app) (∼· ∼refl (aβ g))))

--- The reassociation appearing in the abs case of close

swp : {n : ℕ} {Γ : Con n} {A B D : Ty n} → Tm Γ ((A × B) × D , (A × D) × B)
swp = pair (pair (fst · fst) snd) (fst · snd)

-- close (abs t) is abs (swp · close t)
swapSwap : {n : ℕ} {Γ : Con n} {A B D : Ty n} → swp {Γ = Γ} {A = A} {B} {D} · swp {A = A} {D} {B} ∼ id
swapSwap = ∼trans (pairComp swp (pair (fst · fst) snd) (fst · snd))
  (∼trans (∼pair (pairComp swp (fst · fst) snd) ∼refl)
  (∼trans (∼pair (∼pair (∼sym (assoc swp fst fst)) ∼refl) (∼sym (assoc swp fst snd)))
  (∼trans (∼pair (∼pair (∼· swp·fst ∼refl) swp·snd) (∼· swp·fst ∼refl))
  (∼trans (∼pair (∼pair (pfst (fst · fst) snd) ∼refl) (psnd (fst · fst) snd))
  (∼trans (∼pair (∼sym (pairComp fst fst snd)) ∼refl)
  (∼trans (∼pair (∼· ∼refl pairId) ∼refl)
  (∼trans (∼pair (unitr fst) ∼refl) pairId)))))))
  where
  swp·fst : {n : ℕ} {Γ : Con n} {A B D : Ty n} → swp {Γ = Γ} {A = A} {B} {D} · fst ∼ pair (fst · fst) snd
  swp·fst = pfst (pair (fst · fst) snd) (fst · snd)
  swp·snd : {n : ℕ} {Γ : Con n} {A B D : Ty n} → swp {Γ = Γ} {A = A} {B} {D} · snd ∼ fst · snd
  swp·snd = psnd (pair (fst · fst) snd) (fst · snd)

--- close respects the equivalence

-- The common shape of the aβ and aext cases: close (pair (fst · e) snd · app),
-- where h is close e
closeApp : {n : ℕ} {Γ : Con n} {A B C D : Ty n} (h : Tm Γ (A × D , B ⇒ C)) →
           pair (pair (pair (fst · fst) snd · h) (fst · snd)) snd · (fst · app) ∼ swp · (pair (fst · h) snd · app)
closeApp h = ∼trans (∼sym (assoc (pair (pair (pair (fst · fst) snd · h) (fst · snd)) snd) fst app))
  (∼trans (∼· (pfst (pair (pair (fst · fst) snd · h) (fst · snd)) snd) ∼refl)
  (∼sym (∼trans (∼sym (assoc swp (pair (fst · h) snd) app))
        (∼· (∼trans (pairComp swp (fst · h) snd)
                    (∼pair (∼trans (∼sym (assoc swp fst h)) (∼· (pfst (pair (fst · fst) snd) (fst · snd)) ∼refl))
                           (psnd (pair (fst · fst) snd) (fst · snd))))
             ∼refl))))

close∼ : {n : ℕ} {Γ : Con n} {A B C : Ty n} {t u : Tm (Γ ▹ (𝟙 , A)) (B , C)} → t ∼ u → close t ∼ close u
close∼ (pfst f g) =
  ∼trans (∼sym (assoc (pair (pair (close f) (close g)) snd) fst fst))
  (∼trans (∼· (pfst (pair (close f) (close g)) snd) ∼refl) (pfst (close f) (close g)))
close∼ (psnd f g) =
  ∼trans (∼sym (assoc (pair (pair (close f) (close g)) snd) fst snd))
  (∼trans (∼· (pfst (pair (close f) (close g)) snd) ∼refl) (psnd (close f) (close g)))
close∼ (pext f) = ∼trans (pext (close f)) (∼pair
  (∼sym (∼trans (∼sym (assoc (pair (close f) snd) fst fst)) (∼· (pfst (close f) snd) ∼refl)))
  (∼sym (∼trans (∼sym (assoc (pair (close f) snd) fst snd)) (∼· (pfst (close f) snd) ∼refl))))
close∼ (text f) = text (close f)
close∼ (aβ f) = ∼trans (closeApp (abs (swp · close f)))
  (∼trans (∼· ∼refl (aβ (swp · close f)))
  (∼trans (∼sym (assoc swp swp (close f))) (∼trans (∼· swapSwap ∼refl) (unitl (close f)))))
close∼ (aext f) = ∼trans (aext (close f)) (∼abs
  (∼sym (∼trans (∼· ∼refl (closeApp (close f)))
        (∼trans (∼sym (assoc swp swp (pair (fst · close f) snd · app)))
        (∼trans (∼· swapSwap ∼refl) (unitl (pair (fst · close f) snd · app)))))))
close∼ (unitl f) = ∼trans (∼· pairId ∼refl) (unitl (close f))
close∼ (unitr f) = pfst (close f) snd
close∼ (assoc f g h) =
  ∼trans (∼· (∼trans (∼pair ∼refl (∼sym (psnd (close f) snd))) (∼sym (pairComp (pair (close f) snd) (close g) snd))) ∼refl)
         (assoc (pair (close f) snd) (pair (close g) snd) (close h))
close∼ (∼· p q) = ∼· (∼pair (close∼ p) ∼refl) (close∼ q)
close∼ (∼pair p q) = ∼pair (close∼ p) (close∼ q)
close∼ (∼abs p) = ∼abs (∼· ∼refl (close∼ p))
close∼ ∼refl = ∼refl
close∼ (∼sym p) = ∼sym (close∼ p)
close∼ (∼trans p q) = ∼trans (close∼ p) (close∼ q)

-- Binding a variable which does not occur amounts to a projection
closeRen : {n : ℕ} {Γ : Con n} {A B C : Ty n} (t : Tm Γ (B , C)) → close {A = A} (ren wkRen t) ∼ fst · t
closeRen (var x) = ∼refl
closeRen id = ∼sym (unitr fst)
closeRen (f · g) =
  ∼trans (∼· (∼pair (closeRen f) ∼refl) (closeRen g))
  (∼trans (∼sym (assoc (pair (fst · f) snd) fst g))
  (∼trans (∼· (pfst (fst · f) snd) ∼refl) (assoc fst f g)))
closeRen term = ∼sym (text (fst · term))
closeRen (pair f g) = ∼trans (∼pair (closeRen f) (closeRen g)) (∼sym (pairComp fst f g))
closeRen fst = ∼refl
closeRen snd = ∼refl
closeRen (abs t) =
  ∼trans (∼abs (∼· ∼refl (closeRen t)))
  (∼trans (∼abs (∼trans (∼sym (assoc swp fst t)) (∼· (pfst (pair (fst · fst) snd) (fst · snd)) ∼refl)))
          (∼sym (absComp fst t)))
closeRen app = ∼refl

-- Applying a function to the freshly bound variable: the inverse of close
opn : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (𝟙 , A ⇒ B) → Tm (Γ ▹ (𝟙 , A)) (𝟙 , B)
opn t = pair (ren wkRen t) (term · var here) · app

closeOpn : {n : ℕ} {Γ : Con n} {A B : Ty n} (t : Tm Γ (𝟙 , A ⇒ B)) → close (opn t) ∼ pair (fst · t) snd · app
closeOpn t =
  ∼trans (∼· (∼pair (∼pair (closeRen t) (psnd term snd)) ∼refl) ∼refl)
  (∼trans (∼sym (assoc (pair (pair (fst · t) snd) snd) fst app))
          (∼· (pfst (pair (fst · t) snd) snd) ∼refl))

-- η in the form produced by reification
closeOpn∼ : {n : ℕ} {Γ : Con n} {A B : Ty n} (t : Tm Γ (𝟙 , A ⇒ B)) → t ∼ abs (close (opn t))
closeOpn∼ t = ∼trans (aext t) (∼abs (∼sym (closeOpn t)))

--- The logical relation between terms and values

R : {n : ℕ} {Γ : Con n} (A : Ty n) → Tm Γ (𝟙 , A) → ⟦ A ⟧ Γ → Type
R (X x) t (u , _) = t ∼ u
R 𝟙 t v = Unit
R (A × B) t (a , b) = R A (t · fst) a ∧ R B (t · snd) b
R {Γ = Γ} (A ⇒ B) t f =
  {Δ : Con _} (ρ : Ren Γ Δ) {u : Tm Δ (𝟙 , A)} {a : ⟦ A ⟧ Δ} → R A u a → R B (pair (ren ρ t) u · app) (f ρ a)

-- The relation only depends on the term up to equivalence
R∼ : {n : ℕ} {Γ : Con n} (A : Ty n) {t t' : Tm Γ (𝟙 , A)} {v : ⟦ A ⟧ Γ} → t ∼ t' → R A t v → R A t' v
R∼ (X x) p r = ∼trans (∼sym p) r
R∼ 𝟙 p r = tt
R∼ (A × B) p (r , s) = R∼ A (∼· p ∼refl) r , R∼ B (∼· p ∼refl) s
R∼ (A ⇒ B) p r = λ ρ q → R∼ B (∼· (∼pair (ren∼ ρ p) ∼refl) ∼refl) (r ρ q)

-- ... and is stable under renaming
Rwk : {n : ℕ} {Γ Δ : Con n} (A : Ty n) (ρ : Ren Γ Δ) {t : Tm Γ (𝟙 , A)} {v : ⟦ A ⟧ Γ} → R A t v → R A (ren ρ t) (⟦⟧wk A ρ v)
Rwk (X x) ρ r = ren∼ ρ r
Rwk 𝟙 ρ r = tt
Rwk (A × B) ρ (r , s) = Rwk A ρ r , Rwk B ρ s
Rwk (A ⇒ B) ρ {t = t} r = λ ρ' {u} q →
  subst (λ s → R B (pair s u · app) _) (sym (renComp ρ' ρ t)) (r (ρ' ∘R ρ) q)

--- Reification is sound and reflection is complete

reifyR : {n : ℕ} {Γ : Con n} (A : Ty n) {t : Tm Γ (𝟙 , A)} {v : ⟦ A ⟧ Γ} → R A t v → t ∼ proj₁ (reify A v)
reflectR : {n : ℕ} {Γ : Con n} (A : Ty n) {t : Tm Γ (𝟙 , A)} {u : Ne Γ A} → t ∼ proj₁ u → R A t (reflect A u)

reifyR (X x) r = r
reifyR 𝟙 {t = t} r = text t
reifyR (A × B) {t = t} (r , s) = ∼trans (pext t) (∼pair (reifyR A r) (reifyR B s))
-- the body is reified in the extended context, then closed back: this is where
-- close∼ is needed, to rewrite underneath the binder
reifyR (A ⇒ B) {t = t} r = ∼trans (closeOpn∼ t)
  (∼abs (close∼ (reifyR B (r wkRen (reflectR A {u = term · var here , neu-var can-term here} ∼refl)))))

reflectR (X x) p = p
reflectR 𝟙 p = tt
reflectR (A × B) p = reflectR A (∼· p ∼refl) , reflectR B (∼· p ∼refl)
reflectR (A ⇒ B) p = λ ρ q → reflectR B (∼· (∼pair (ren∼ ρ p) (reifyR _ q)) ∼refl)

--- The fundamental lemma: evaluation preserves the logical relation

evalR : {n : ℕ} {Γ : Con n} {A B : Ty n} (t : Tm Γ (A , B)) {Δ : Con n} (ρ : Ren Γ Δ) {u : Tm Δ (𝟙 , A)} {v : ⟦ A ⟧ Δ} →
        R A u v → R B (u · ren ρ t) (eval t ρ v)
evalR {A = A} {B} (var x) ρ r = reflectR B (∼· (reifyR A r) ∼refl)
evalR id ρ {u = u} r = R∼ _ (∼sym (unitr u)) r
evalR (f · g) ρ {u = u} r = R∼ _ (assoc u (ren ρ f) (ren ρ g)) (evalR g ρ (evalR f ρ r))
evalR term ρ r = tt
evalR (pair f g) ρ {u = u} r =
  R∼ _ (∼sym (∼trans (assoc u (pair (ren ρ f) (ren ρ g)) fst) (∼· ∼refl (pfst (ren ρ f) (ren ρ g))))) (evalR f ρ r) ,
  R∼ _ (∼sym (∼trans (assoc u (pair (ren ρ f) (ren ρ g)) snd) (∼· ∼refl (psnd (ren ρ f) (ren ρ g))))) (evalR g ρ r)
evalR fst ρ r = proj₁ r
evalR snd ρ r = proj₂ r
evalR {A = A} (abs f) ρ {u = u} r = λ ρ' {w} q →
  R∼ _ (∼sym (absβ (ren ρ' u) w (ren ρ' (ren ρ f))))
    (subst (λ F → R _ (pair (ren ρ' u) w · F) ?) (sym (renComp ρ' ρ f))
      (evalR f (ρ' ∘R ρ)
        ( R∼ A (∼sym (pfst (ren ρ' u) w)) (Rwk A ρ' r)
        , R∼ _ (∼sym (psnd (ren ρ' u) w)) q )))
evalR {B = B} app ρ {u = u} (r , s) =
  R∼ B (∼· (∼sym (pext u)) ∼refl)
    (subst (λ h → R B (pair h (u · snd) · app) ?) (renId (u · fst)) (r idRen s))

--- Soundness

nf∼ : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → t ∼ nf t
nf∼ {A = A} t = ∼trans (∼trans (∼sym (unitl t)) (∼· (text id) ∼refl))
  (reifyR A (subst (λ s → R A (term · s) (eval t idRen tt)) (renId t) (evalR t idRen tt)))

--- Sanity checks

-- Normalization is the identity on the canonical term of a pasting scheme:
-- this is nfCan combined with the uniqueness of canonical terms, and holds
-- with no computation involved
nfPSTm : {n : ℕ} {Γ : Con n} {A : Ty n} (ps : PS Γ A) → nf (PSTmTm ps) ≡ PSTmTm ps
nfPSTm ps = CanUniq ps (nfCan (PSTmTm ps))

module _ where
  private
    -- One generator 𝟙 → X, whence a term of type X
    Γ₁ : Con 1
    Γ₁ = ε ▹ (𝟙 , X (# 0))

    x : Tm Γ₁ (𝟙 , X (# 0))
    x = term · var here

    -- The identity function, in η-long form
    idf : Tm Γ₁ (𝟙 , X (# 0) ⇒ X (# 0))
    idf = ren wkRen (PSTmTm PS⊢X⇒X')

    -- β: applying the identity to x gives back x
    _ : nf (pair idf x · app) ≡ x
    _ = refl

    -- η: abs snd is the identity function but is not canonical (its body, var
    -- here, is not), so it normalizes to the η-long form
    _ : nf (abs snd) ≡ idf
    _ = refl
