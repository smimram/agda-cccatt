--- Categorical combinators for cartesian categories
--- (we might add closure someday)

open import Prelude
open import Ty

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var : {A : Arr n} → A ∈ Γ → Tm Γ A
  id : {A : Ty n} → Tm Γ (A , A)
  _·_ : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pair : {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
  cfst : {A B : Ty n} → Tm Γ (A × B , A)
  csnd : {A B : Ty n} → Tm Γ (A × B , B)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  pfst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · cfst ∼ f
  psnd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · csnd ∼ g
  pext : {X A B : Ty n} (f : Tm Γ (X , A × B)) → pair (f · cfst) (f · csnd) ∼ f
  -- pext : {A B : Ty n} → pair cfst csnd ∼ id {A = A × B}
  text : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  pnat : {A' A B C : Ty n} (f : Tm Γ (A' , A)) (g : Tm Γ (A , B)) (h : Tm Γ (A , C)) → f · pair g h ∼ pair (f · g) (f · h)
  ∼refl : {A : Arr n} {t : Tm Γ A} → t ∼ t
  ∼sym : {A : Arr n} {t u : Tm Γ A} → t ∼ u → u ∼ t
  ∼trans : {A : Arr n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v

-- postulate
  -- -- TODO: we do not formalize pasting schemes for now and simply assume that pasting schemes are contractible
  -- PSTm : {n : ℕ} {Γ : Con n} {A : Ty n} → PS Γ A → Tm Γ A
  -- PSEq : {n : ℕ} {Γ : Con n} {A : Ty n} (ps : PS Γ A) (t u : Tm Γ A) → t ∼ u

-- -- Substitutions
-- Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
-- -- Sub _ Γ ε = Unit
-- -- Sub τ Γ (Γ' ▹ A) = Sub τ Γ Γ' × Tm Γ (A [ τ ]')

-- -- Terminal substitution
-- SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
-- -- SubTerm Γ = tt

-- -- Application of a substitution
-- _[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A : Ty n'} → Tm Γ' A → {τ : SubTy n n'} (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]')
-- -- var here [ σ , t ] = t
-- -- var (drop x) [ σ , t ] = var x [ σ ]
-- -- I [ σ ] = I
-- -- K [ σ ] = K
-- -- S [ σ ] = S
-- -- (t $ u) [ σ ] = t [ σ ] $ u [ σ ]

-- -- Equivalence of substitutions
-- _∼Sub_ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ σ' : Sub τ Γ Γ') → Type
-- -- _∼Sub_ {Γ' = ε} tt tt = Unit
-- -- _∼Sub_ {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (σ ∼Sub σ') × (t ∼ t')

-- ∼SubRefl : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ : Sub τ Γ Γ') → σ ∼Sub σ
-- -- ∼SubRefl {Γ' = ε} σ = tt
-- -- ∼SubRefl {Γ' = Γ' ▹ A} (σ , t) = ∼SubRefl σ , ∼refl

-- ∼SubSym : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → σ' ∼Sub σ
-- -- ∼SubSym {Γ' = ε} tt = tt
-- -- ∼SubSym {Γ' = Γ' ▹ A} (p , q) = ∼SubSym p , ∼sym q

-- _[_]∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ∼ u → σ ∼Sub σ' → t [ σ ] ∼ u [ σ' ]
-- -- _[_]∼ {σ = σ} {σ'} (Iβ t) q = ∼trans (Iβ (t [ σ ])) ((∼refl {t = t}) [ q ]∼)
-- -- _[_]∼ {σ = σ} {σ'} (Kβ t u) q = ∼trans (Kβ (t [ σ ]) (u [ σ ])) ((∼refl {t = t}) [ q ]∼)
-- -- _[_]∼ {σ = σ} {σ'} (Sβ t u v) q = ∼trans (∼$ (∼$ (∼$ ∼refl ((∼refl {t = t}) [ q ]∼)) ((∼refl {t = u}) [ q ]∼)) ((∼refl {t = v}) [ q ]∼)) (Sβ (t [ σ' ]) (u [ σ' ]) (v [ σ' ]))
-- -- _[_]∼ lamIβ q = lamIβ
-- -- _[_]∼ lamKβ q = lamKβ
-- -- _[_]∼ lamSβ q = lamSβ
-- -- _[_]∼ lamwk q = lamwk
-- -- _[_]∼ lamη q = lamη
-- -- _[_]∼ (∼$ p p') q = ∼$ (p [ q ]∼) (p' [ q ]∼)
-- -- _[_]∼ {t = t} ∼refl q = lem t q
  -- -- where
  -- -- lem : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
  -- -- lem (var here) (σ , p) = p
  -- -- lem (var (drop x)) (σ , p) = lem (var x) σ
  -- -- lem I σ = ∼refl
  -- -- lem K σ = ∼refl
  -- -- lem S σ = ∼refl
  -- -- lem (t $ u) σ = ∼$ (lem t σ) (lem u σ)
-- -- _[_]∼ {σ = σ} {σ'} (∼sym p) q = ∼sym (p [ ∼SubSym q ]∼)
-- -- _[_]∼ {σ = σ} {σ'} (∼trans p p') q = ∼trans (p [ q ]∼) (p' [ ∼SubRefl σ' ]∼)

-- -- Composition of substitutions
-- _∘_ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} → Sub τ' Γ' Γ'' → Sub τ Γ Γ' → Sub (τ' ∘' τ) Γ Γ''
-- -- _∘_ {Γ'' = ε} σ' σ = tt
-- -- _∘_ {Γ'' = Γ'' ▹ A} (σ' , t') σ = (σ' ∘ σ) , (t' [ σ ])

-- -- Functoriality of substitution application
-- [∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Ty n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (t : Tm Γ'' A) (σ' : Sub τ' Γ' Γ'') (σ : Sub τ Γ Γ') →
      -- -- subst (Tm Γ) ([∘'] {A = A} {τ' = τ'} {τ = τ}) (t [ σ' ] [ σ ]) ≡ t [ σ' ∘ σ ]
      -- t [ σ' ] [ σ ] ≡ t [ σ' ∘ σ ]
-- -- [∘] (var here) (σ' , t) σ = refl
-- -- [∘] (var (drop x)) (σ' , t) σ = [∘] (var x) σ' σ
-- -- [∘] I σ' σ = refl
-- -- [∘] K σ' σ = refl
-- -- [∘] S σ' σ = refl
-- -- [∘] (t $ u) σ' σ = cong₂ _$_ ([∘] t σ' σ) ([∘] u σ' σ)
