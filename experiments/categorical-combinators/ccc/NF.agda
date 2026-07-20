--- Normalization by evaluation for cartesian closed categories
---
--- Every term with source 𝟙 is equivalent to a canonical (βη-long) one. Here we
--- construct the normal form and show that it is canonical; the fact that it is
--- equivalent to the original term is still postulated at the end of the file.

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

-- Remaining gap: the normal form is equivalent to the original term. This
-- requires a logical relation between terms and values, together with a β-law
-- for close.
postulate
  nf∼ : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → t ∼ nf t

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
