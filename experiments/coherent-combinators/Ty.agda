open import Prelude

infixr 6 _×_
infixr 5 _⇒_

-- Types
data Ty (n : ℕ) : Type where
  X   : Fin n → Ty n
  𝟙   : Ty n
  _×_ : (A B : Ty n) → Ty n
  _⇒_ : (A B : Ty n) → Ty n
