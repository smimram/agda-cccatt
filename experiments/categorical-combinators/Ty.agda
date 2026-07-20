open import Prelude

{-# BUILTIN REWRITE _≡_ #-}

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

-- A substitution on types
SubTy : ℕ → ℕ → Set
SubTy n n' = Vec (Ty n) n'

-- Applying a type substitution
_[_]' : {n : ℕ} {n' : ℕ} → Ty n' → SubTy n n' → Ty n
X x [ σ ]' = lookup σ x
𝟙 [ τ ]' = 𝟙
(A × B) [ τ ]' = A [ τ ]' × B [ τ ]'
(A ⇒ B) [ τ ]' = A [ τ ]' ⇒ B [ τ ]'

WkTy : {n : ℕ} → Ty n → Ty (suc n)
WkTy (X x) = X (suc x)
WkTy 𝟙 = 𝟙
WkTy (A × B) = WkTy A × WkTy B
WkTy (A ⇒ B) = WkTy A ⇒ WkTy B

SubTyWk : {n n' : ℕ} → SubTy n n' → SubTy (suc n) n'
SubTyWk τ = map WkTy τ

SubTyId : (n : ℕ) → SubTy n n
SubTyId zero = []
SubTyId (suc n) = X zero ∷ SubTyWk (SubTyId n)

SubTyIdEq : {n : ℕ} {A : Ty n} → A [ SubTyId n ]' ≡ A
SubTyIdEq {n} {A = X x} = lookup-id x
  where
  lookup-map-weaken : {n n' : ℕ} {σ : SubTy n n'} (x : Fin n') {y : Fin n} → lookup σ x ≡ X y → lookup (SubTyWk σ) x ≡ X (suc y)
  lookup-map-weaken {σ = σ} x {y} p =
    lookup (SubTyWk σ) x  ≡⟨⟩
    lookup (map WkTy σ) x ≡⟨ lookup-map x WkTy σ ⟩
    WkTy (lookup σ x)     ≡⟨ cong WkTy p ⟩
    WkTy (X y)            ≡⟨⟩
    X (suc y)             ∎
  lookup-id : {n : ℕ} (x : Fin n) → lookup (SubTyId n) x ≡ X x
  lookup-wk : {n : ℕ} (x : Fin n) → lookup (SubTyWk (SubTyId n)) x ≡ X (suc x)
  lookup-id zero = refl
  lookup-id (suc x) = lookup-wk x
  lookup-wk zero = refl
  lookup-wk (suc x) = lookup-map-weaken {σ = SubTyWk (SubTyId _)} x (lookup-id (suc x))
SubTyIdEq {A = 𝟙} = refl
SubTyIdEq {A = A × B} = cong₂ _×_ SubTyIdEq SubTyIdEq
SubTyIdEq {A = A ⇒ B} = cong₂ _⇒_ SubTyIdEq SubTyIdEq

{-# REWRITE SubTyIdEq #-}

SubTy1 : {n : ℕ} (A : Ty n) → SubTy n 1
SubTy1 A = A ∷ []

SubTy2 : {n : ℕ} (A B : Ty n) → SubTy n 2
SubTy2 A B = A ∷ B ∷ []

SubTy3 : {n : ℕ} (A B C : Ty n) → SubTy n 3
SubTy3 A B C = A ∷ B ∷ C ∷ []

SubTy4 : {n : ℕ} (A B C D : Ty n) → SubTy n 4
SubTy4 A B C D = A ∷ B ∷ C ∷ D ∷ []

-- Composition of substitutions
_∘'_ : {n n' n'' : ℕ} → SubTy n' n'' → SubTy n n' → SubTy n n''
-- τ' ∘' τ = map (λ A → A [ τ ]') τ'
[] ∘' τ = []
(A ∷ τ') ∘' τ = A [ τ ]' ∷ (τ' ∘' τ)

SubTyUnitL : {n n' : ℕ} (τ : SubTy n n') → SubTyId n' ∘' τ ≡ τ
SubTyUnitL {n} {n'} τ = {!!} -- standard material

-- Applying a substition is an action
[∘'] : {n n' n'' : ℕ} {A : Ty n''} {τ : SubTy n n'} {τ' : SubTy n' n''} → (A [ τ' ]' [ τ ]') ≡ (A [ τ' ∘' τ ]')
[∘'] {A = X zero} {τ' = τ' ∷ _} = refl
[∘'] {n} {n'} {n''} {A = X (suc x)} {τ} {τ' = A ∷ τ'} = [∘'] {A = X x} {τ = τ} {τ' = τ'}
[∘'] {A = 𝟙} = refl
[∘'] {A = A × B} = cong₂ _×_ ([∘'] {A = A}) ([∘'] {A = B})
[∘'] {A = A ⇒ B} = cong₂ _⇒_ ([∘'] {A = A}) ([∘'] {A = B})

{-# REWRITE [∘'] #-}
{-# REWRITE SubTyUnitL #-}

-- Contexts
data Con (n : ℕ) : Set where
  ε : Con n
  _▹_ : (Γ : Con n) (A : Arr n) → Con n

infixl 5 _▹_

-- Presence in contexts
data _∈_ {n : ℕ} (A : Arr n) : Con n → Set where
  here : {Γ : Con n} → A ∈ (Γ ▹ A)
  drop : {Γ : Con n} {B : Arr n} → A ∈ Γ → A ∈ (Γ ▹ B)

-- postulate
  -- -- TODO: we do not formalize pasting schemes for now and simply assume that the necessary types are pasting
  -- PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set

  -- PS⊢X⇒X : PS {n = 1} ε (X (# 0) , X (# 0))
  -- PSX⇒Y,Y⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ ((X (# 0)) , (X (# 1))) ▹ (X (# 1) , X (# 2))) (X (# 0) , X (# 2))
  -- PSX⇒Y⊢X⇒Y : PS {n = 2} (ε ▹ (X (# 0) , X (# 1))) (X (# 0) , X (# 1))

  -- PS⊢X⇒1 : PS {n = 1} ε (X (# 0) , 𝟙)
  -- PSX⇒1⊢X⇒1 : PS {n = 1} (ε ▹ (X (# 0) , 𝟙)) (X (# 0) , 𝟙)
  -- PS⊢X×Y⇒X : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 0))
  -- PS⊢X×Y⇒Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 1))
  -- PS⊢X×Y⇒X×Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 0) × X (# 1))
  -- PSX⇒Y,X⇒Z⊢X⇒Y×Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1) × X (# 2))
  -- PSX⇒Y,X⇒Z⊢X⇒Y : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1))
  -- PSX⇒Y,X⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 2))

  -- -- PS⊢X⇒Y⇒X : PS {n = 2} ε (X (# 0) ⇒ X (# 1) ⇒ X (# 0))
  -- -- PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z : PS {n = 3} ε ((X (# 0) ⇒ X (# 1) ⇒ X (# 2)) ⇒ (X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 2))
  -- -- PSX⊢X : PS {n = 1} (ε ▹ X (# 0)) (X (# 0))
  -- -- PSX,Y⊢X : PS {n = 2} (ε ▹ X (# 0) ▹ X (# 1)) (X (# 0))
  -- -- -- PSX⇒Y⇒Z,X⇒Y,X⊢Z : PS {n = 3} (ε ▹ (X (# 0) ⇒ X (# 1) ⇒ X (# 2)) ▹ (X (# 0) ⇒ X (# 1)) ▹ X (# 0)) (X (# 2))
  -- -- PSX⇒Y,X⊢Y : PS {n = 2} (ε ▹ (X (# 0) ⇒ X (# 1)) ▹ X (# 0)) (X (# 1))
  -- -- PS⊢[X⇒Y]⇒X⇒Y : PS {n = 2} ε ((X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 1))
  -- -- PS⊢[X⇒Z]⇒[X⇒Y]⇒[X⇒Z] : PS {n = 3} ε ((X (# 0) ⇒ X (# 2)) ⇒ (X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 2))
  -- -- PS⊢[X⇒Z]⇒X⇒Y⇒Z : PS {n = 3} ε ((X (# 0) ⇒ X (# 2)) ⇒ X (# 0) ⇒ X (# 1) ⇒ X (# 2))
  -- -- PS⊢[X⇒Y⇒Z⇒W]⇒[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒W : PS {n = 4} ε ((X (# 0) ⇒ X (# 1) ⇒ X (# 2) ⇒ X (# 3)) ⇒ (X (# 0) ⇒ X (# 1) ⇒ X (# 2)) ⇒ (X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 3))
