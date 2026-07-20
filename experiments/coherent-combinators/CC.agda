-- Categorical combinators

open import Prelude
open import Ty

infixl 7 _·_

data Tm {n : ℕ} (Γ : Con n) : Ty n → Type where
  var  : {A : Ty n} → A ∈ Γ → Tm Γ (𝟙 ⇒ A)
  id   : {A : Ty n} → Tm Γ (A ⇒ A)
  _·_  : {A B C : Ty n} → Tm Γ (A ⇒ B) → Tm Γ (B ⇒ C) → Tm Γ (A ⇒ C)
  term : {A : Ty n} → Tm Γ (A ⇒ 𝟙)
  pair : {Z A B : Ty n} → Tm Γ (Z ⇒ A) → Tm Γ (Z ⇒ B) → Tm Γ (Z ⇒ A × B)
  fst  : {A B : Ty n} → Tm Γ (A × B ⇒ A)
  snd  : {A B : Ty n} → Tm Γ (A × B ⇒ B)
  abs  : {A B C : Ty n} → Tm Γ (A × B ⇒ C) → Tm Γ (A ⇒ B ⇒ C)
  app  : {A B : Ty n} → Tm Γ ((A ⇒ B) × A ⇒ B)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Ty n} → Tm Γ A → Tm Γ A → Type where
  pfst : {Z A B : Ty n} (f : Tm Γ (Z ⇒ A)) (g : Tm Γ (Z ⇒ B)) → pair f g · fst ∼ f
  psnd : {Z A B : Ty n} (f : Tm Γ (Z ⇒ A)) (g : Tm Γ (Z ⇒ B)) → pair f g · snd ∼ g
  pext : {A B C : Ty n} (f : Tm Γ (A ⇒ B × C)) → f ∼ pair (f · fst) (f · snd)
  text : {A : Ty n} (f : Tm Γ (A ⇒ 𝟙)) → f ∼ term
  aβ : {A B C : Ty n} (f : Tm Γ (A × B ⇒ C)) → pair (fst · abs f) snd · app ∼ f
  aext : {A B C : Ty n} (f : Tm Γ (A ⇒ B ⇒ C)) → f ∼ abs (pair (fst · f) snd · app)
  unitl : {A B : Ty n} (f : Tm Γ (A ⇒ B)) → id · f ∼ f
  unitr : {A B : Ty n} (f : Tm Γ (A ⇒ B)) → f · id ∼ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A ⇒ B)) (g : Tm Γ (B ⇒ C)) (h : Tm Γ (C ⇒ D)) → (f · g) · h ∼ f · (g · h)
  ∼· : {A B C : Ty n} {f f' : Tm Γ (A ⇒ B)} {g g' : Tm Γ (B ⇒ C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼pair : {Z A B : Ty n} {f f' : Tm Γ (Z ⇒ A)} {g g' : Tm Γ (Z ⇒ B)} → f ∼ f' → g ∼ g' → pair f g ∼ pair f' g'
  ∼abs : {A B C : Ty n} {f f' : Tm Γ (A × B ⇒ C)} → f ∼ f' → abs f ∼ abs f'
  ∼refl : {A : Ty n} {f : Tm Γ A} → f ∼ f
  ∼sym  : {A : Ty n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Ty n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h

-- Equational reasoning for ∼

module ∼-Reasoning {n : ℕ} {Γ : Con n} where

  infix  1 begin∼_
  infixr 2 _∼⟨_⟩_ _∼⟨_⟨_ _∼⟨⟩_
  infix  3 _∎∼

  begin∼_ : {A : Ty n} {f g : Tm Γ A} → f ∼ g → f ∼ g
  begin∼ p = p

  _∼⟨_⟩_ : {A : Ty n} (f : Tm Γ A) {g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h
  _ ∼⟨ p ⟩ q = ∼trans p q

  -- same, with the step used backwards
  _∼⟨_⟨_ : {A : Ty n} (f : Tm Γ A) {g h : Tm Γ A} → g ∼ f → g ∼ h → f ∼ h
  _ ∼⟨ p ⟨ q = ∼trans (∼sym p) q

  _∼⟨⟩_ : {A : Ty n} (f : Tm Γ A) {g : Tm Γ A} → f ∼ g → f ∼ g
  _ ∼⟨⟩ p = p

  _∎∼ : {A : Ty n} (f : Tm Γ A) → f ∼ f
  _ ∎∼ = ∼refl

-- Derived laws

module _ {n : ℕ} {Γ : Con n} where

  -- composition distributes over pairing
  ·pair : {Z A B C : Ty n} (h : Tm Γ (Z ⇒ A)) (f : Tm Γ (A ⇒ B)) (g : Tm Γ (A ⇒ C)) →
          h · pair f g ∼ pair (h · f) (h · g)
  ·pair h f g = ∼trans (pext (h · pair f g)) (∼pair
    (∼trans (assoc h (pair f g) fst) (∼· ∼refl (pfst f g)))
    (∼trans (assoc h (pair f g) snd) (∼· ∼refl (psnd f g))))

  -- β for abstraction, in the form used to translate the CL β-rules
  appβ : {Z A B C : Ty n} (u : Tm Γ (Z ⇒ A)) (v : Tm Γ (Z ⇒ B)) (h : Tm Γ (A × B ⇒ C)) →
         pair (u · abs h) v · app ∼ pair u v · h
  appβ u v h = ∼trans
    (∼· (∼sym (∼trans (·pair (pair u v) (fst · abs h) snd) (∼pair
      (∼trans (∼sym (assoc (pair u v) fst (abs h))) (∼· (pfst u v) ∼refl))
      (psnd u v)))) ∼refl)
    (∼trans (assoc (pair u v) (pair (fst · abs h) snd) app) (∼· ∼refl (aβ h)))
