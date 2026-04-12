open import Prelude
open import Ty

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
  start : PS {n = 1} ε (X (# 0) , X (# 0))
  ext   : {n : ℕ} {Γ : Con n} {A B : Ty n} → PS Γ (A , B) → PS {n = suc n} (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0))

PS⊢X⇒X : PS {n = 1} ε (X (# 0) , X (# 0))
PS⊢X⇒X = start

PSX⇒Y⊢X⇒Y : PS {n = 2} (ε ▹ (X (# 1) , X (# 0))) (X (# 1) , X (# 0))
PSX⇒Y⊢X⇒Y = ext start

PSX⇒Y,Y⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ ((X (# 2)) , (X (# 1))) ▹ (X (# 1) , X (# 0))) (X (# 2) , X (# 0))
PSX⇒Y,Y⇒Z⊢X⇒Z = ext (ext start)
