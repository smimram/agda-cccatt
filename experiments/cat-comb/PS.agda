open import Prelude
open import Data.List
open import Ty hiding (PS)

-- List of variables occurring as targets
targets : {n : ℕ} (A : Ty n) → List (Fin n)
targets (X x) = x ∷ []
targets 𝟙 = []
targets (A × B) = targets A ++ targets B

targetsCon : {n : ℕ} (Γ : Con n) → List (Fin n)
targetsCon ε = []
targetsCon (Γ ▹ (_ , A)) = targets A ++ targetsCon Γ

-- PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set
-- PS Γ (A , X x) = {!!}
-- PS Γ (A , 𝟙) = Unit
-- PS Γ (A , B × C) = PS Γ (A , B) ∧ PS Γ (A , C)

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
  -- start : {n : ℕ} {Γ : Con n} (xs
