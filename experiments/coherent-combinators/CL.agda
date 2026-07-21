-- Simply-typed combinatory logic

open import Prelude
open import Ty

infixl 6 _$_

data Tm {n : ℕ} (Γ : Con' n) : Ty n → Type where
  var : {A : Ty n} → A ∈' Γ → Tm Γ A
  I   : {A : Ty n} → Tm Γ (A ⇒ A)
  K   : {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A)
  S   : {A B C : Ty n} → Tm Γ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  P₁  : {A B : Ty n} → Tm Γ (A × B ⇒ A)
  P₂  : {A B : Ty n} → Tm Γ (A × B ⇒ B)
  P   : {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A × B)
  T   : Tm Γ 𝟙
  _$_ : {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con' n} : {A : Ty n} → Tm Γ A → Tm Γ A → Type where
  Iβ : {A : Ty n} (t : Tm Γ A) → I $ t ∼ t
  Kβ : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → K $ t $ u ∼ t
  Sβ : {A B C : Ty n} (t : Tm Γ (A ⇒ B ⇒ C)) (u : Tm Γ (A ⇒ B)) (v : Tm Γ A) → S $ t $ u $ v ∼ t $ v $ (u $ v)
  P₁β : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → P₁ $ (P $ t $ u) ∼ t
  P₂β : {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → P₂ $ (P $ t $ u) ∼ u
  Pη : {A B : Ty n} (t : Tm Γ (A × B)) → t ∼ P $ (P₁ $ t) $ (P₂ $ t)
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
  -- The `lam*` rule for the terminal object: bracket abstraction of CC's `text`
  -- axiom, `lam_a (a) ∼ lam_a (K $ T)`.  This is the one terminal primitive; the
  -- η-rule `Tη`, `lamT`, and the schematic `lamTη` are all derived from it below.
  lamText : {A : Ty n} → _∼_ {A = (A ⇒ 𝟙) ⇒ A ⇒ 𝟙}
            I
            (K $ (K $ T))
  ∼$ : {A B : Ty n} {t t' : Tm Γ (A ⇒ B)} {u u' : Tm Γ A} → t ∼ t' → u ∼ u' → t $ u ∼ t' $ u'
  ∼refl : {A : Ty n} {t : Tm Γ A} → t ∼ t
  ∼sym : {A : Ty n} {t u : Tm Γ A} → t ∼ u → u ∼ t
  ∼trans : {A : Ty n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v

-- Equational reasoning for ∼

module ∼-Reasoning {n : ℕ} {Γ : Con' n} where

  infix  1 begin∼_
  infixr 2 _∼⟨_⟩_ _∼⟨⟩_
  infix  3 _∎∼

  begin∼_ : {A : Ty n} {t u : Tm Γ A} → t ∼ u → t ∼ u
  begin∼ p = p

  _∼⟨_⟩_ : {A : Ty n} (t : Tm Γ A) {u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v
  _ ∼⟨ p ⟩ q = ∼trans p q

  _∼⟨⟩_ : {A : Ty n} (t : Tm Γ A) {u : Tm Γ A} → t ∼ u → t ∼ u
  _ ∼⟨⟩ p = p

  _∎∼ : {A : Ty n} (t : Tm Γ A) → t ∼ t
  _ ∎∼ = ∼refl

-- Weakening

wk : {n : ℕ} {Γ : Con' n} {A B : Ty n} → Tm Γ B → Tm (Γ ▹' A) B
wk (var x) = var (drop' x)
wk I = I
wk K = K
wk S = S
wk P₁ = P₁
wk P₂ = P₂
wk P = P
wk T = T
wk (t $ u) = wk t $ wk u

-- Bracket abstraction (the Λx.- of the course notes).  The clause
-- "Λx.T = K T when x ∉ FV(T)" has no de Bruijn counterpart -- there is no
-- occurrence test on `Tm (Γ ▹' A) B` -- so it is recovered below as the lemma
-- `lamwk`, rather than being definitional.

lam : {n : ℕ} {Γ : Con' n} {A B : Ty n} → Tm (Γ ▹' A) B → Tm Γ (A ⇒ B)
lam (var here') = I
lam (var (drop' x)) = K $ var x
lam I = K $ I
lam K = K $ K
lam S = K $ S
lam P₁ = K $ P₁
lam P₂ = K $ P₂
lam P = K $ P
lam T = K $ T
lam (t $ u) = S $ lam t $ lam u

-- Bracket abstraction is well-behaved: the ξ rule and η, from which functional
-- extensionality follows.  This is the (ζ) rule of the course notes (§3.6.3,
-- lemma 3.6.3.11), which is equivalent to full extensionality; the point is
-- that it is *admissible* here rather than assumed, and the `lam*` equations
-- above are exactly the finite axiom set that makes it so.

module _ {n : ℕ} {Γ : Con' n} where

  open ∼-Reasoning

  -- `lamwk` in applied form: this is the clause "Λx.T = K T when x ∉ FV(T)" of
  -- the usual bracket abstraction, which cannot be definitional with de Bruijn
  -- indices since there is no occurrence test.
  lamK$ : {A B C : Ty n} (t : Tm Γ (A ⇒ C)) (u : Tm Γ A) →
          _∼_ {A = B ⇒ C} (S $ (K $ t) $ (K $ u)) (K $ (t $ u))
  lamK$ t u = begin∼
    S $ (K $ t) $ (K $ u)
      ∼⟨ ∼sym redL ⟩
    S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K))) $ (K $ K) $ t $ u
      ∼⟨ ∼$ (∼$ lamwk ∼refl) ∼refl ⟩
    S $ (K $ K) $ t $ u
      ∼⟨ Sβ _ _ _ ⟩
    K $ K $ u $ (t $ u)
      ∼⟨ ∼$ (Kβ _ _) ∼refl ⟩
    K $ (t $ u) ∎∼
    where
      redL : (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K))) $ (K $ K) $ t $ u)
             ∼ (S $ (K $ t) $ (K $ u))
      redL = begin∼
        S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K))) $ (K $ K) $ t $ u
          ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
        S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K)) $ t $ (K $ K $ t) $ u
          ∼⟨ ∼$ (∼$ (Sβ _ _ _) (Kβ _ _)) ∼refl ⟩
        K $ S $ t $ (S $ (K $ K) $ (S $ (K $ S) $ K) $ t) $ K $ u
          ∼⟨ ∼$ (∼$ (∼$ (Kβ _ _) (Sβ _ _ _)) ∼refl) ∼refl ⟩
        S $ (K $ K $ t $ (S $ (K $ S) $ K $ t)) $ K $ u
          ∼⟨ ∼$ (∼$ (∼$ ∼refl (∼$ (Kβ _ _) (Sβ _ _ _))) ∼refl) ∼refl ⟩
        S $ (K $ (K $ S $ t $ (K $ t))) $ K $ u
          ∼⟨ ∼$ (∼$ (∼$ ∼refl (∼$ ∼refl (∼$ (Kβ _ _) ∼refl))) ∼refl) ∼refl ⟩
        S $ (K $ (S $ (K $ t))) $ K $ u
          ∼⟨ Sβ _ _ _ ⟩
        K $ (S $ (K $ t)) $ u $ (K $ u)
          ∼⟨ ∼$ (Kβ _ _) ∼refl ⟩
        S $ (K $ t) $ (K $ u) ∎∼

  -- Abstracting a term in which the variable does not occur.
  lam-wk : {A B : Ty n} (s : Tm Γ B) → lam {A = A} (wk s) ∼ K $ s
  lam-wk (var x) = ∼refl
  lam-wk I = ∼refl
  lam-wk K = ∼refl
  lam-wk S = ∼refl
  lam-wk P₁ = ∼refl
  lam-wk P₂ = ∼refl
  lam-wk P = ∼refl
  lam-wk T = ∼refl
  lam-wk (t $ u) = begin∼
    S $ lam (wk t) $ lam (wk u)
      ∼⟨ ∼$ (∼$ ∼refl (lam-wk t)) (lam-wk u) ⟩
    S $ (K $ t) $ (K $ u)
      ∼⟨ lamK$ t u ⟩
    K $ (t $ u) ∎∼

  -- η on the right: `lamη` applied to a single argument.
  etaR : {A B : Ty n} (h : Tm Γ (A ⇒ B)) → (S $ (K $ h) $ I) ∼ h
  etaR h = ∼trans (∼sym red) (∼trans (∼$ lamη ∼refl) (Iβ h))
    where
      red : (S $ (S $ (K $ S) $ K) $ (K $ I) $ h) ∼ (S $ (K $ h) $ I)
      red = begin∼
        S $ (S $ (K $ S) $ K) $ (K $ I) $ h
          ∼⟨ Sβ _ _ _ ⟩
        S $ (K $ S) $ K $ h $ (K $ I $ h)
          ∼⟨ ∼$ (Sβ _ _ _) (Kβ _ _) ⟩
        K $ S $ h $ (K $ h) $ I
          ∼⟨ ∼$ (∼$ (Kβ _ _) ∼refl) ∼refl ⟩
        S $ (K $ h) $ I ∎∼

  -- η: abstracting a variable that was just applied.
  lam-η : {A B : Ty n} (h : Tm Γ (A ⇒ B)) → lam (wk h $ var here') ∼ h
  lam-η h = begin∼
    S $ lam (wk h) $ I
      ∼⟨ ∼$ (∼$ ∼refl (lam-wk h)) ∼refl ⟩
    S $ (K $ h) $ I
      ∼⟨ etaR h ⟩
    h ∎∼

  -- Pointwise behaviour of the combinator towers that the translation G
  -- produces: applying each of them to an argument.

  comp$ : {A B C : Ty n} (b : Tm Γ (B ⇒ C)) (a : Tm Γ (A ⇒ B)) (x : Tm Γ A) →
          (S $ (K $ b) $ a $ x) ∼ (b $ (a $ x))
  comp$ b a x = ∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)

  pair$ : {C A B : Ty n} (a : Tm Γ (C ⇒ A)) (b : Tm Γ (C ⇒ B)) (x : Tm Γ C) →
          (S $ (S $ (K $ P) $ a) $ b $ x) ∼ (P $ (a $ x) $ (b $ x))
  pair$ a b x = ∼trans (Sβ _ _ _) (∼$ (comp$ P a x) ∼refl)

  abs$ : {A B C : Ty n} (h : Tm Γ (A × B ⇒ C)) (x : Tm Γ A) →
         (S $ (K $ (S $ (K $ h))) $ P $ x) ∼ (S $ (K $ h) $ (P $ x))
  abs$ h x = comp$ (S $ (K $ h)) P x

  app$ : {A B : Ty n} (x : Tm Γ ((A ⇒ B) × A)) →
         (S $ P₁ $ P₂ $ x) ∼ (P₁ $ x $ (P₂ $ x))
  app$ x = Sβ P₁ P₂ x

  -- The product rules in "pointwise" form: these are `lamP₁`, `lamP₂`, `lamP`
  -- applied to arguments.  They are what both the ξ rule below and the
  -- translation of the categorical product axioms need.

  pfst∼ : {C A B : Ty n} (a : Tm Γ (C ⇒ A)) (b : Tm Γ (C ⇒ B)) →
          (S $ (K $ P₁) $ (S $ (S $ (K $ P) $ a) $ b)) ∼ a
  pfst∼ a b = ∼trans (∼sym red) (∼trans (∼$ (∼$ lamP₁ ∼refl) ∼refl) (Kβ a b))
    where
      red : (S $ (K $ (S $ (K $ (S $ (K $ P₁))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ a $ b)
            ∼ (S $ (K $ P₁) $ (S $ (S $ (K $ P) $ a) $ b))
      red = begin∼
        S $ (K $ (S $ (K $ (S $ (K $ P₁))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ a $ b
          ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
        K $ (S $ (K $ (S $ (K $ P₁)))) $ a $ (S $ (K $ S) $ (S $ (K $ P)) $ a) $ b
          ∼⟨ ∼$ (∼$ (Kβ _ _) (Sβ _ _ _)) ∼refl ⟩
        S $ (K $ (S $ (K $ P₁))) $ (K $ S $ a $ (S $ (K $ P) $ a)) $ b
          ∼⟨ ∼$ (∼$ ∼refl (∼$ (Kβ _ _) ∼refl)) ∼refl ⟩
        S $ (K $ (S $ (K $ P₁))) $ (S $ (S $ (K $ P) $ a)) $ b
          ∼⟨ Sβ _ _ _ ⟩
        K $ (S $ (K $ P₁)) $ b $ (S $ (S $ (K $ P) $ a) $ b)
          ∼⟨ ∼$ (Kβ _ _) ∼refl ⟩
        S $ (K $ P₁) $ (S $ (S $ (K $ P) $ a) $ b) ∎∼

  psnd∼ : {C A B : Ty n} (a : Tm Γ (C ⇒ A)) (b : Tm Γ (C ⇒ B)) →
          (S $ (K $ P₂) $ (S $ (S $ (K $ P) $ a) $ b)) ∼ b
  psnd∼ a b =
    ∼trans (∼sym red)
      (∼trans (∼$ (∼$ lamP₂ ∼refl) ∼refl) (∼trans (∼$ (Kβ I a) ∼refl) (Iβ b)))
    where
      red : (S $ (K $ (S $ (K $ (S $ (K $ P₂))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ a $ b)
            ∼ (S $ (K $ P₂) $ (S $ (S $ (K $ P) $ a) $ b))
      red = begin∼
        S $ (K $ (S $ (K $ (S $ (K $ P₂))))) $ (S $ (K $ S) $ (S $ (K $ P))) $ a $ b
          ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
        K $ (S $ (K $ (S $ (K $ P₂)))) $ a $ (S $ (K $ S) $ (S $ (K $ P)) $ a) $ b
          ∼⟨ ∼$ (∼$ (Kβ _ _) (Sβ _ _ _)) ∼refl ⟩
        S $ (K $ (S $ (K $ P₂))) $ (K $ S $ a $ (S $ (K $ P) $ a)) $ b
          ∼⟨ ∼$ (∼$ ∼refl (∼$ (Kβ _ _) ∼refl)) ∼refl ⟩
        S $ (K $ (S $ (K $ P₂))) $ (S $ (S $ (K $ P) $ a)) $ b
          ∼⟨ Sβ _ _ _ ⟩
        K $ (S $ (K $ P₂)) $ b $ (S $ (S $ (K $ P) $ a) $ b)
          ∼⟨ ∼$ (Kβ _ _) ∼refl ⟩
        S $ (K $ P₂) $ (S $ (S $ (K $ P) $ a) $ b) ∎∼

  pext∼ : {C A B : Ty n} (a : Tm Γ (C ⇒ A × B)) →
          a ∼ (S $ (S $ (K $ P) $ (S $ (K $ P₁) $ a)) $ (S $ (K $ P₂) $ a))
  pext∼ a = begin∼
    a
      ∼⟨ ∼sym (Iβ a) ⟩
    I $ a
      ∼⟨ ∼sym (∼$ lamP ∼refl) ⟩
    S $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁)))) $ (S $ (K $ P₂)) $ a
      ∼⟨ Sβ _ _ _ ⟩
    S $ (K $ S) $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁))) $ a $ (S $ (K $ P₂) $ a)
      ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
    K $ S $ a $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁)) $ a) $ (S $ (K $ P₂) $ a)
      ∼⟨ ∼$ (∼$ (Kβ _ _) (Sβ _ _ _)) ∼refl ⟩
    S $ (K $ (S $ (K $ P)) $ a $ (S $ (K $ P₁) $ a)) $ (S $ (K $ P₂) $ a)
      ∼⟨ ∼$ (∼$ ∼refl (∼$ (Kβ _ _) ∼refl)) ∼refl ⟩
    S $ (S $ (K $ P) $ (S $ (K $ P₁) $ a)) $ (S $ (K $ P₂) $ a) ∎∼

  -- The terminal object.  `lamText` is the single primitive; `lamTη` ("A ⇒ 𝟙 is
  -- terminal"), `Tη` ("𝟙 is terminal") and `lamT` all follow from it, using only
  -- the β-rules -- no `funext`, so there is no circularity.

  lamTη : {A : Ty n} (h : Tm Γ (A ⇒ 𝟙)) → h ∼ K $ T
  lamTη h = ∼trans (∼sym (Iβ h)) (∼trans (∼$ lamText ∼refl) (Kβ (K $ T) h))

  Tη : (t : Tm Γ 𝟙) → t ∼ T
  Tη t = ∼trans (∼sym (Kβ t T)) (∼trans (∼$ (lamTη (K $ t)) ∼refl) (Kβ T T))

  lamT : _∼_ {A = 𝟙 ⇒ 𝟙} (K $ T) I
  lamT = ∼sym (lamTη I)

  -- The ξ rule: bracket abstraction is compatible with the equivalence.  The
  -- induction is on the derivation, and each CL axiom is discharged by exactly
  -- one `lam*` rule -- which is what that family of rules is for.
  ξ : {A B : Ty n} {t u : Tm (Γ ▹' A) B} → t ∼ u → lam t ∼ lam u

  ξ (Iβ t) = ∼trans (∼$ lamIβ ∼refl) (Iβ (lam t))

  ξ (Kβ t u) =
    ∼trans (∼sym red) (∼trans (∼$ (∼$ lamKβ ∼refl) ∼refl) (Kβ (lam t) (lam u)))
    where
      red : (S $ (K $ S) $ (S $ (K $ K)) $ lam t $ lam u)
            ∼ (S $ (S $ (K $ K) $ lam t) $ lam u)
      red = ∼$ (∼trans (Sβ _ _ _) (∼$ (Kβ _ _) ∼refl)) ∼refl

  ξ (Sβ t u v) =
    ∼trans (∼sym redL) (∼trans (∼$ (∼$ (∼$ lamSβ ∼refl) ∼refl) ∼refl) redR)
    where
      a = lam t ; b = lam u ; c = lam v

      redL : (S $ (K $ (S $ (K $ S))) $ (S $ (K $ S) $ (S $ (K $ S))) $ a $ b $ c)
             ∼ (S $ (S $ (S $ (K $ S) $ a) $ b) $ c)
      redL = begin∼
        S $ (K $ (S $ (K $ S))) $ (S $ (K $ S) $ (S $ (K $ S))) $ a $ b $ c
          ∼⟨ ∼$ (∼$ (Sβ _ _ _) ∼refl) ∼refl ⟩
        K $ (S $ (K $ S)) $ a $ (S $ (K $ S) $ (S $ (K $ S)) $ a) $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ (Kβ _ _) (Sβ _ _ _)) ∼refl) ∼refl ⟩
        S $ (K $ S) $ (K $ S $ a $ (S $ (K $ S) $ a)) $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ ∼refl (∼$ (Kβ _ _) ∼refl)) ∼refl) ∼refl ⟩
        S $ (K $ S) $ (S $ (S $ (K $ S) $ a)) $ b $ c
          ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
        K $ S $ b $ (S $ (S $ (K $ S) $ a) $ b) $ c
          ∼⟨ ∼$ (∼$ (Kβ _ _) ∼refl) ∼refl ⟩
        S $ (S $ (S $ (K $ S) $ a) $ b) $ c ∎∼

      redR : (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S)))) $ (K $ S) $ a $ b $ c)
             ∼ (S $ (S $ a $ c) $ (S $ b $ c))
      redR = begin∼
        S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S)))) $ (K $ S) $ a $ b $ c
          ∼⟨ ∼$ (∼$ (Sβ _ _ _) ∼refl) ∼refl ⟩
        S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S))) $ a $ (K $ S $ a) $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ (Sβ _ _ _) (Kβ _ _)) ∼refl) ∼refl ⟩
        K $ S $ a $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S)) $ a) $ S $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ (∼$ (Kβ _ _) (Sβ _ _ _)) ∼refl) ∼refl) ∼refl ⟩
        S $ (K $ K $ a $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S) $ a)) $ S $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ (∼$ ∼refl (∼$ (Kβ _ _) (Sβ _ _ _))) ∼refl) ∼refl) ∼refl ⟩
        S $ (K $ (K $ S $ a $ (S $ (K $ (S $ (K $ S))) $ S $ a))) $ S $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ (∼$ ∼refl (∼$ ∼refl (∼$ (Kβ _ _) (Sβ _ _ _)))) ∼refl) ∼refl) ∼refl ⟩
        S $ (K $ (S $ (K $ (S $ (K $ S)) $ a $ (S $ a)))) $ S $ b $ c
          ∼⟨ ∼$ (∼$ (∼$ (∼$ ∼refl (∼$ ∼refl (∼$ ∼refl (∼$ (Kβ _ _) ∼refl)))) ∼refl) ∼refl) ∼refl ⟩
        S $ (K $ (S $ (S $ (K $ S) $ (S $ a)))) $ S $ b $ c
          ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
        K $ (S $ (S $ (K $ S) $ (S $ a))) $ b $ (S $ b) $ c
          ∼⟨ ∼$ (∼$ (Kβ _ _) ∼refl) ∼refl ⟩
        S $ (S $ (K $ S) $ (S $ a)) $ (S $ b) $ c
          ∼⟨ Sβ _ _ _ ⟩
        S $ (K $ S) $ (S $ a) $ c $ (S $ b $ c)
          ∼⟨ ∼$ (Sβ _ _ _) ∼refl ⟩
        K $ S $ c $ (S $ a $ c) $ (S $ b $ c)
          ∼⟨ ∼$ (∼$ (Kβ _ _) ∼refl) ∼refl ⟩
        S $ (S $ a $ c) $ (S $ b $ c) ∎∼

  ξ (P₁β t u) = pfst∼ (lam t) (lam u)
  ξ (P₂β t u) = psnd∼ (lam t) (lam u)
  ξ (Pη t) = pext∼ (lam t)

  -- The `lam*` rules are equations between closed towers of constants, so both
  -- sides are weakenings and `lam-wk` reduces the goal to the rule itself.
  ξ lamIβ = ∼trans (lam-wk (S $ (K $ I))) (∼trans (∼$ ∼refl lamIβ) (∼sym (lam-wk I)))
  ξ lamKβ = ∼trans (lam-wk (S $ (K $ S) $ (S $ (K $ K)))) (∼trans (∼$ ∼refl lamKβ) (∼sym (lam-wk K)))
  ξ lamSβ = ∼trans (lam-wk (S $ (K $ (S $ (K $ S))) $ (S $ (K $ S) $ (S $ (K $ S)))))
              (∼trans (∼$ ∼refl lamSβ)
                (∼sym (lam-wk (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S)))) $ (K $ S)))))
  ξ lamwk = ∼trans (lam-wk (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K))) $ (K $ K)))
              (∼trans (∼$ ∼refl lamwk) (∼sym (lam-wk (S $ (K $ K)))))
  ξ lamη = ∼trans (lam-wk (S $ (S $ (K $ S) $ K) $ (K $ I))) (∼trans (∼$ ∼refl lamη) (∼sym (lam-wk I)))
  ξ lamP₁ = ∼trans (lam-wk (S $ (K $ (S $ (K $ (S $ (K $ P₁))))) $ (S $ (K $ S) $ (S $ (K $ P)))))
              (∼trans (∼$ ∼refl lamP₁) (∼sym (lam-wk K)))
  ξ lamP₂ = ∼trans (lam-wk (S $ (K $ (S $ (K $ (S $ (K $ P₂))))) $ (S $ (K $ S) $ (S $ (K $ P)))))
              (∼trans (∼$ ∼refl lamP₂) (∼sym (lam-wk (K $ I))))
  ξ lamP = ∼trans (lam-wk (S $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ P))) $ (S $ (K $ P₁)))) $ (S $ (K $ P₂))))
             (∼trans (∼$ ∼refl lamP) (∼sym (lam-wk I)))
  ξ lamText = ∼trans (lam-wk I) (∼trans (∼$ ∼refl lamText) (∼sym (lam-wk (K $ (K $ T)))))

  ξ (∼$ p q) = ∼$ (∼$ ∼refl (ξ p)) (ξ q)
  ξ ∼refl = ∼refl
  ξ (∼sym p) = ∼sym (ξ p)
  ξ (∼trans p q) = ∼trans (ξ p) (ξ q)

  -- Functional extensionality -- the (ζ) rule of the course notes: two terms of
  -- arrow type are equivalent as soon as they agree on a fresh variable.  `ξ` is
  -- now total, so this is a complete proof.
  funext : {A B : Ty n} {h h' : Tm Γ (A ⇒ B)} →
           (wk h $ var here') ∼ (wk h' $ var here') → h ∼ h'
  funext {h = h} {h' = h'} p = ∼trans (∼sym (lam-η h)) (∼trans (ξ p) (lam-η h'))
