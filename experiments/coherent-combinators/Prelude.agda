open import Agda.Primitive public using (Level) renaming (Set to Type ; lzero to ℓ-zero ; lsuc to ℓ-suc ; _⊔_ to ℓ-max)
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open ≡-Reasoning public
open import Data.Nat public
open import Data.Fin using (Fin ; zero ; suc ; #_) public
