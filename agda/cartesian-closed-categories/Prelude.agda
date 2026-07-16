open import Agda.Primitive public using (Level) renaming (Set to Type ; lzero to ℓ-zero ; lsuc to ℓ-suc ; _⊔_ to ℓ-max)
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open ≡-Reasoning public
open import Data.Nat public
open import Data.Fin using (Fin ; zero ; suc ; #_) public
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; map) public
open import Data.Vec.Properties using (lookup-map) public
open import Data.Unit hiding (_≟_) renaming (⊤ to Unit) public
open import Data.Product hiding (map) renaming (proj₁ to fst ; proj₂ to snd) public
open import Data.Product.Properties public

infixr 30 _∙_
_∙_ = trans

substConst : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {x y : A} (p : x ≡ y) (b : B) → subst (λ _ → B) p b ≡ b
substConst refl b = refl
