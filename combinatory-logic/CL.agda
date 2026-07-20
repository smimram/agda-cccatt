--- Combinatory logic for the implicational fragment

open import Prelude
open import Ty

infixl 6 _$_

data Tm {n : ℕ} (Γ : Con n) : Ty n → Type where
  var : {A : Ty n} → A ∈ Γ → Tm Γ A
  I   : {A : Ty n} → Tm Γ (A ⇒ A)
  K   : {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A)
  S   : {A B C : Ty n} → Tm Γ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  P₁  : {A B : Ty n} → Tm Γ (A × B ⇒ A)
  P₂  : {A B : Ty n} → Tm Γ (A × B ⇒ B)
  P   : {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A × B)
  T   : Tm Γ 𝟙
  _$_ : {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Ty n} → Tm Γ A → Tm Γ A → Type where
  Iβ : {A : Ty n} (t : Tm Γ A) → I $ t ∼ t
  Kβ : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → K $ t $ u ∼ t
  Sβ : {A B C : Ty n} (t : Tm Γ (A ⇒ B ⇒ C)) (u : Tm Γ (A ⇒ B)) (v : Tm Γ A) → S $ t $ u $ v ∼ t $ v $ (u $ v)
  P₁β : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → P₁ $ (P $ t $ u) ∼ t
  P₂β : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → P₂ $ (P $ t $ u) ∼ u
  Pη : {A B : Ty n} (t : Tm Γ (A × B)) → t ∼ P $ (P₁ $ t) $ (P₂ $ t)
  Tη : (t : Tm Γ 𝟙) → t ∼ T
  lamIβ : {A B : Ty n} → _∼_ {A = (A ⇒ B) ⇒ A ⇒ B}
          (S $ (K $ I))
          I
  lamKβ : {A B C : Ty n} → _∼_ {A = (A ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C}
          (S $ (K $ S) $ (S $ (K $ K)))
          K
  lamSβ : {A B C D : Ty n} → _∼_ {A = (A ⇒ B ⇒ C ⇒ D) ⇒ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ D}
          ((S $ (K $ (S $ (K $ S))) $ (S $ (K $ S) $ (S $ (K $ S)))))
          ((S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S)))) $ (K $ S)))
  lamwk : {A B C : Ty n} → _∼_ {A = (A ⇒ C) ⇒ A ⇒ B ⇒ C}
          (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K))) $ (K $ K))
          (S $ (K $ K))
  lamη : {A B : Ty n} → _∼_ {A = ((A ⇒ B) ⇒ A ⇒ B)}
         (S $ (S $ (K $ S) $ K) $ (K $ I))
         I
  lamP₁ : {A B C : Ty n} → _∼_ {A = (A ⇒ B) ⇒ (A ⇒ C) ⇒ A ⇒ B}
          (S $ (K $ (S $ (K $ (S $ (K $ P₁))))) $ (S $ (K $ S) $ (S $ (K $ P))))
          K
  lamP₂ : {A B C : Ty n} → _∼_ {A = (A ⇒ B) ⇒ (A ⇒ C) ⇒ A ⇒ C}
          (S $ (K $ (S $ (K $ (S $ (K $ P₂))))) $ (S $ (K $ S) $ (S $ (K $ P))))
          (K $ I)
  lamP : {A B C : Ty n} → _∼_ {A = (A ⇒ B × C) ⇒ A ⇒ B × C}
         (S $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁)))) $ (S $ (K $ P₂)))
         I
  lamT : (K $ T) ∼ I
  ∼$ : {A B : Ty n} {t t' : Tm Γ (A ⇒ B)} {u u' : Tm Γ A} → t ∼ t' → u ∼ u' → t $ u ∼ t' $ u'
  ∼refl : {A : Ty n} {t : Tm Γ A} → t ∼ t
  ∼sym : {A : Ty n} {t u : Tm Γ A} → t ∼ u → u ∼ t
  ∼trans : {A : Ty n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v

postulate
  -- TODO: we do not formalize pasting schemes for now and simply assume that pasting schemes are contractible
  PSTm : {n : ℕ} {Γ : Con n} {A : Ty n} → PS Γ A → Tm Γ A
  PSEq : {n : ℕ} {Γ : Con n} {A : Ty n} (ps : PS Γ A) (t u : Tm Γ A) → t ∼ u

-- Substitutions
Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
Sub _ Γ ε = Unit
Sub τ Γ (Γ' ▹ A) = Sub τ Γ Γ' ∧ Tm Γ (A [ τ ]')

-- Terminal substitution
SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
SubTerm Γ = tt

-- Application of a substitution
_[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A : Ty n'} → Tm Γ' A → {τ : SubTy n n'} (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]')
var here [ σ , t ] = t
var (drop x) [ σ , t ] = var x [ σ ]
I [ σ ] = I
K [ σ ] = K
S [ σ ] = S
P₁ [ σ ] = P₁
P₂ [ σ ] = P₂
P [ σ ] = P
T [ σ ] = T
(t $ u) [ σ ] = t [ σ ] $ u [ σ ]

-- Equivalence of substitutions
_∼Sub_ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ σ' : Sub τ Γ Γ') → Type
_∼Sub_ {Γ' = ε} tt tt = Unit
_∼Sub_ {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (σ ∼Sub σ') ∧ (t ∼ t')

∼SubRefl : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ : Sub τ Γ Γ') → σ ∼Sub σ
∼SubRefl {Γ' = ε} σ = tt
∼SubRefl {Γ' = Γ' ▹ A} (σ , t) = ∼SubRefl σ , ∼refl

∼SubSym : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → σ' ∼Sub σ
∼SubSym {Γ' = ε} tt = tt
∼SubSym {Γ' = Γ' ▹ A} (p , q) = ∼SubSym p , ∼sym q

_[_]∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ∼ u → σ ∼Sub σ' → t [ σ ] ∼ u [ σ' ]
_[_]∼ {σ = σ} {σ'} (Iβ t) q = ∼trans (Iβ (t [ σ ])) ((∼refl {t = t}) [ q ]∼)
_[_]∼ {σ = σ} {σ'} (Kβ t u) q = ∼trans (Kβ (t [ σ ]) (u [ σ ])) ((∼refl {t = t}) [ q ]∼)
_[_]∼ {σ = σ} {σ'} (Sβ t u v) q = ∼trans (∼$ (∼$ (∼$ ∼refl ((∼refl {t = t}) [ q ]∼)) ((∼refl {t = u}) [ q ]∼)) ((∼refl {t = v}) [ q ]∼)) (Sβ (t [ σ' ]) (u [ σ' ]) (v [ σ' ]))
_[_]∼ {σ = σ} {σ'} (P₁β t u) q = ∼trans (P₁β (t [ σ ]) (u [ σ ])) ((∼refl {t = t}) [ q ]∼)
_[_]∼ {σ = σ} {σ'} (P₂β t u) q = ∼trans (P₂β (t [ σ ]) (u [ σ ])) ((∼refl {t = u}) [ q ]∼)
_[_]∼ {σ = σ} {σ'} (Pη t) q = ∼trans ((∼refl {t = t}) [ q ]∼) (Pη (t [ σ' ]))
_[_]∼ {σ = σ} {σ'} (Tη t) q = Tη (t [ σ ])
_[_]∼ lamIβ q = lamIβ
_[_]∼ lamKβ q = lamKβ
_[_]∼ lamSβ q = lamSβ
_[_]∼ lamwk q = lamwk
_[_]∼ lamη q = lamη
_[_]∼ lamP₁ q = lamP₁
_[_]∼ lamP₂ q = lamP₂
_[_]∼ lamP q = lamP
_[_]∼ lamT q = lamT
_[_]∼ (∼$ p p') q = ∼$ (p [ q ]∼) (p' [ q ]∼)
_[_]∼ {t = t} ∼refl q = lem t q
  where
  lem : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
  lem (var here) (σ , p) = p
  lem (var (drop x)) (σ , p) = lem (var x) σ
  lem I σ = ∼refl
  lem K σ = ∼refl
  lem S σ = ∼refl
  lem P₁ σ = ∼refl
  lem P₂ σ = ∼refl
  lem P σ = ∼refl
  lem T σ = ∼refl
  lem (t $ u) σ = ∼$ (lem t σ) (lem u σ)
_[_]∼ {σ = σ} {σ'} (∼sym p) q = ∼sym (p [ ∼SubSym q ]∼)
_[_]∼ {σ = σ} {σ'} (∼trans p p') q = ∼trans (p [ q ]∼) (p' [ ∼SubRefl σ' ]∼)

-- Composition of substitutions
_∘_ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} → Sub τ' Γ' Γ'' → Sub τ Γ Γ' → Sub (τ' ∘' τ) Γ Γ''
_∘_ {Γ'' = ε} tt σ = tt
_∘_ {Γ'' = Γ'' ▹ A} (σ' , t') σ = (σ' ∘ σ) , (t' [ σ ])

-- Functoriality of substitution application
[∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Ty n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (t : Tm Γ'' A) (σ' : Sub τ' Γ' Γ'') (σ : Sub τ Γ Γ') →
      -- subst (Tm Γ) ([∘'] {A = A} {τ' = τ'} {τ = τ}) (t [ σ' ] [ σ ]) ≡ t [ σ' ∘ σ ]
      t [ σ' ] [ σ ] ≡ t [ σ' ∘ σ ]
[∘] (var here) (σ' , t) σ = refl
[∘] (var (drop x)) (σ' , t) σ = [∘] (var x) σ' σ
[∘] I σ' σ = refl
[∘] K σ' σ = refl
[∘] S σ' σ = refl
[∘] P₁ σ' σ = refl
[∘] P₂ σ' σ = refl
[∘] P σ' σ = refl
[∘] T σ' σ = refl
[∘] (t $ u) σ' σ = cong₂ _$_ ([∘] t σ' σ) ([∘] u σ' σ)
