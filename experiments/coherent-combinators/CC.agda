-- Categorical combinators

open import Prelude
open import Ty

data Tm {n : ℕ} (Γ : Con n) : Ty n → Type where
  var  : {A : Ty n} → A ∈ Γ → Tm Γ A
  term : {A : Ty n} → Tm Γ 𝟙
  pair : {A B : Ty n} → Tm Γ A → Tm Γ B → Tm Γ (A × B)
  fst  : {A B : Ty n} → Tm Γ (A × B ⇒ A)
  snd  : {A B : Ty n} → Tm Γ (A × B ⇒ B)
  abs  : {A B C : Ty n} → Tm Γ (A × B ⇒ C) → Tm Γ (A ⇒ B ⇒ C)
  app  : {A B : Ty n} → Tm Γ ((A ⇒ B) × A ⇒ B)

infix 5 _∼_

-- data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  -- pfst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · fst ∼ f
  -- psnd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · snd ∼ g
  -- pext : {A B C : Ty n} (f : Tm Γ (A , B × C)) → f ∼ pair (f · fst) (f · snd)
  -- text : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
  -- aβ : {A B C : Ty n} (f : Tm Γ (A × B , C)) → pair (fst · abs f) snd · app ∼ f
  -- aext : {A B C : Ty n} (f : Tm Γ (A , B ⇒ C)) → f ∼ abs (pair (fst · f) snd · app)
  -- unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  -- unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  -- assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  -- ∼· : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  -- ∼pair : {X A B : Ty n} {f f' : Tm Γ (X , A)} {g g' : Tm Γ (X , B)} → f ∼ f' → g ∼ g' → pair f g ∼ pair f' g'
  -- ∼abs : {A B C : Ty n} {f f' : Tm Γ (A × B , C)} → f ∼ f' → abs f ∼ abs f'
  -- ∼refl : {A : Arr n} {f : Tm Γ A} → f ∼ f
  -- ∼sym  : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  -- ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h
