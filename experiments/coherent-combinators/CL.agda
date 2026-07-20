-- Simply-typed combinatory logic

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
