open import Prelude
open import Data.List
open import Ty hiding (PS)
open import CC

-- Canonical terms: in βη-long form
data canonical {n : ℕ} : {Γ : Con n} {A : Arr n} (t : Tm Γ A) → Type where
  can-hom : {Γ : Con n} {A B : Ty n} (t : Tm Γ (𝟙 , A ⇒ B)) → canonical t → canonical {A = A , B} {!!}
  

  -- var  : {A : Arr n} → A ∈ Γ → Tm Γ A
  -- can-abs : {Γ : Con n} {A B C : Ty n} {t : Tm _ (B , C)} → canonical (Γ ▹ (𝟙 , A)) t → canonical Γ {!!}
  -- can-pair : {Γ : Con n} {A B C : Ty n} → 

-- A variable does not occur in the target of a type
hasNoTarget : {n : ℕ} (x : Fin n) (A : Ty n) → Type
hasNoTarget x (X y) = x ≢ y
hasNoTarget x 𝟙 = ⊤
hasNoTarget x (A × B) = hasNoTarget x A ∧ hasNoTarget x B
hasNoTarget x (A ⇒ B) = hasNoTarget x A ∧ hasNoTarget x B

-- A variable occurs exactly once in the target of a type
data hasTarget {n : ℕ} (x : Fin n) : Ty n → Type where
  targetX : hasTarget x (X x)
  targetL : {A B : Ty n} → hasTarget x A → hasNoTarget x B → hasTarget x (A × B)
  targetR : {A B : Ty n} → hasNoTarget x A → hasTarget x B → hasTarget x (A × B)
  target⇒ : {A B : Ty n} → hasTarget x B → hasTarget x (A ⇒ B)

-- PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set
-- PS Γ (A , X x) = {!!}
-- PS Γ (A , 𝟙) = Unit
-- PS Γ (A , B × C) = PS Γ (A , B) ∧ PS Γ (A , C)

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
  -- start : {n : ℕ} {Γ : Con n} (xs
