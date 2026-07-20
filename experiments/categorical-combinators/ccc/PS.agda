open import Prelude
open import Data.List
open import Ty hiding (PS)
open import CC

-- Bind the last variable of the context
close : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm (Γ ▹ (𝟙 , A)) (B , C) → Tm Γ (B × A , C)
close (var here) = snd
close (var (drop x)) = fst · var x
close id = fst
close (f · g) = pair (close f) snd · close g
close term = term
close (pair f g) = pair (close f) (close g)
close fst = fst · fst
close snd = fst · snd
close (abs t) = abs (pair (pair (fst · fst) snd) (fst · snd) · close t)
close app = fst · app

-- Canonical terms: in βη-long form
data canonical {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type
-- Neutral terms
data neutral {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type

data canonical {n} where
  can-pair : {Γ : Con n} {A B : Ty n} {tl : Tm Γ (𝟙 , A)} {tr : Tm Γ (𝟙 , B)} → canonical tl → canonical tr → canonical {A = A × B} (pair tl tr)
  can-term : {Γ : Con n} → canonical {Γ = Γ} {A = 𝟙} term
  can-abs : {Γ : Con n} {A B : Ty n} {t : Tm (Γ ▹ (𝟙 , A)) (𝟙 , B)} → canonical t → canonical {A = A ⇒ B} (abs (close t))
  can-neu : {Γ : Con n} {x : Fin n} {t : Tm Γ (𝟙 , X x)} → neutral t → canonical {A = X x} t

data neutral {n} where
  neu-var : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A)} → canonical t → (x : (A , B) ∈ Γ) → neutral (t · var x)
  neu-app : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A ⇒ B)} {u : Tm Γ (𝟙 , A)} → neutral t → canonical u → neutral (pair t u · app)
  neu-fst : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · fst)
  neu-snd : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · snd)

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
