open import Prelude

infixr 6 _×_
infixr 5 _⇒_

-- Types
data Ty (n : ℕ) : Type where
  X   : Fin n → Ty n
  𝟙   : Ty n
  _×_ : (A B : Ty n) → Ty n
  _⇒_ : (A B : Ty n) → Ty n

-- An arrow
Arr : ℕ → Type
Arr n = Ty n ∧ Ty n

-- Contexts
data Con (n : ℕ) : Set where
  ε : Con n
  _▹_ : (Γ : Con n) (A : Arr n) → Con n

infixl 5 _▹_

-- Presence in contexts
data _∈_ {n : ℕ} (A : Arr n) : Con n → Set where
  here : {Γ : Con n} → A ∈ (Γ ▹ A)
  drop : {Γ : Con n} {B : Arr n} → A ∈ Γ → A ∈ (Γ ▹ B)

-- Unary contexts
data Con' (n : ℕ) : Set where
  ε' : Con' n
  _▹'_ : (Γ : Con' n) (A : Ty n) → Con' n

infixl 5 _▹'_

data _∈'_ {n : ℕ} (A : Ty n) : Con' n → Set where
  here' : {Γ : Con' n} → A ∈' (Γ ▹' A)
  drop' : {Γ : Con' n} {B : Ty n} → A ∈' Γ → A ∈' (Γ ▹' B)
