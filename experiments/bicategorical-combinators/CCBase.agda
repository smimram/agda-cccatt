open import Prelude
open import Ty
open import PS

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var  : {A : Arr n} → A ∈ Γ → Tm Γ A
  id   : {A : Ty n} → Tm Γ (A , A)
  _·_  : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pa : {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
  fst  : {A B : Ty n} → Tm Γ (A × B , A)
  snd  : {A B : Ty n} → Tm Γ (A × B , B)
  abs  : {A B C : Ty n} → Tm Γ (A × B , C) → Tm Γ (A , B ↝ C)
  app  : {A B : Ty n} → Tm Γ ((A ↝ B) × A , B)

infix 5 _⇒_

data _⇒_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  pa-fst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pa f g · fst ⇒ f
  pa-snd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pa f g · snd ⇒ g
  pa-eta : {A B C : Ty n} (f : Tm Γ (A , B × C)) → f ⇒ pa (f · fst) (f · snd)
  pa2 : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (A , C)} (α : f ⇒ f') (β : g ⇒ g') → pa f g ⇒ pa f' g'
  term-can : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ⇒ term
  eps : {A B C : Ty n} (f : Tm Γ (A × B , C)) → pa (fst · abs f) snd · app ⇒ f
  eta : {A B C : Ty n} (f : Tm Γ (A , B ↝ C)) → f ⇒ abs (pa (fst · f) snd · app)
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ⇒ f
  unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ⇒ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ⇒ f · (g · h)
  ⇒· : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ⇒ f' → g ⇒ g' → f · g ⇒ f' · g'
  ⇒pa : {X A B : Ty n} {f f' : Tm Γ (X , A)} {g g' : Tm Γ (X , B)} → f ⇒ f' → g ⇒ g' → pa f g ⇒ pa f' g'
  ⇒abs : {A B C : Ty n} {f f' : Tm Γ (A × B , C)} → f ⇒ f' → abs f ⇒ abs f'
  ⇒refl : {A : Arr n} {f : Tm Γ A} → f ⇒ f
  ⇒sym  : {A : Arr n} {f g : Tm Γ A} → f ⇒ g → g ⇒ f
  ⇒trans : {A : Arr n} {f g h : Tm Γ A} → f ⇒ g → g ⇒ h → f ⇒ h
  ⇒whiskl : {A B C : Ty n} (f : Tm Γ (A , B)) {g g' : Tm Γ (B , C)} (α : g ⇒ g') → f · g ⇒ f · g'
  ⇒whiskr : {A B C : Ty n} {f f' : Tm Γ (A , B)} (α : f ⇒ f') (g : Tm Γ (B , C)) → f · g ⇒ f' · g

term2 : {n : ℕ} {Γ : Con n} {A : Ty n} (f g : Tm Γ (A , 𝟙)) → f ⇒ g
term2 f g = ⇒trans (term-can f) (⇒sym (term-can g))

data _∼_ {n : ℕ} {Γ : Con n} : {A B : Ty n} {t u : Tm Γ (A , B)} (α β : t ⇒ u) → Type where
  pa2-eta : {A B C : Ty n} {f g : Tm Γ (A , B × C)} (α : f ⇒ g) → ⇒trans α (pa-eta g) ∼ ⇒trans (pa-eta f) (pa2 (⇒whiskr α fst) (⇒whiskr α snd))
  term-can2 : {A : Ty n} {f g : Tm Γ (A , 𝟙)} (α : f ⇒ g) → α ∼ term2 f g
  ∼refl : {A : Arr n} {t u : Tm Γ A} (α : t ⇒ u) → α ∼ α
  -- ∼sym : {A : Arr n} {t u : Tm Γ A} → t ∼ u → u ∼ t
  -- ∼trans : {A : Arr n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v
