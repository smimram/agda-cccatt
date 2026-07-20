-- Categorical combinators

open import Prelude
open import Ty

infixl 7 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var  : {A : Arr n} → A ∈ Γ → Tm Γ A
  id   : {A : Ty n} → Tm Γ (A , A)
  _·_  : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pair : {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
  fst  : {A B : Ty n} → Tm Γ (A × B , A)
  snd  : {A B : Ty n} → Tm Γ (A × B , B)
  abs  : {A B C : Ty n} → Tm Γ (A × B , C) → Tm Γ (A , B ⇒ C)
  app  : {A B : Ty n} → Tm Γ ((A ⇒ B) × A , B)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  pfst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · fst ∼ f
  psnd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · snd ∼ g
  pext : {A B C : Ty n} (f : Tm Γ (A , B × C)) → f ∼ pair (f · fst) (f · snd)
  text : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
  aβ : {A B C : Ty n} (f : Tm Γ (A × B , C)) → pair (fst · abs f) snd · app ∼ f
  aext : {A B C : Ty n} (f : Tm Γ (A , B ⇒ C)) → f ∼ abs (pair (fst · f) snd · app)
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  ∼· : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼pair : {X A B : Ty n} {f f' : Tm Γ (X , A)} {g g' : Tm Γ (X , B)} → f ∼ f' → g ∼ g' → pair f g ∼ pair f' g'
  ∼abs : {A B C : Ty n} {f f' : Tm Γ (A × B , C)} → f ∼ f' → abs f ∼ abs f'
  ∼refl : {A : Arr n} {f : Tm Γ A} → f ∼ f
  ∼sym  : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h

-- Equational reasoning for ∼

module ∼-Reasoning {n : ℕ} {Γ : Con n} where

  infix  1 begin∼_
  infixr 2 _∼⟨_⟩_  _∼⟨⟩_
  infix  3 _∎∼

  begin∼_ : {A : Arr n} {f g : Tm Γ A} → f ∼ g → f ∼ g
  begin∼ p = p

  _∼⟨_⟩_ : {A : Arr n} (f : Tm Γ A) {g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h
  _ ∼⟨ p ⟩ q = ∼trans p q

  _∼⟨⟩_ : {A : Arr n} (f : Tm Γ A) {g : Tm Γ A} → f ∼ g → f ∼ g
  _ ∼⟨⟩ p = p

  _∎∼ : {A : Arr n} (f : Tm Γ A) → f ∼ f
  _ ∎∼ = ∼refl
