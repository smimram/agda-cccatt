open import Prelude
open import Relation.Nullary using (¬_)
open import Ty hiding (PS)
open import CC

-- Bind the last variable of the context
close : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm (Γ ▹ (𝟙 , A)) (B , C) → Tm Γ (B × A , C)
close (var here) = snd
close (var (drop x)) = fst · var x
close id = fst
close (f · g) = pair (close f) snd · close g
close term = term
close (pair f g) = pair (close f) (close g)
close fst = fst · fst
close snd = fst · snd
close (abs t) = abs (pair (pair (fst · fst) snd) (fst · snd) · close t)
close app = fst · app

-- NOTE: we could extend neutral terms to have A as source instead of 𝟙. However, the PS condition would be more difficult to formulate because we can look up stuff both in the context and in the source.

-- Canonical terms: in βη-long form
data canonical {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type
-- Neutral terms
data neutral {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type

data canonical {n} where
  can-pair : {Γ : Con n} {A B : Ty n} {tl : Tm Γ (𝟙 , A)} {tr : Tm Γ (𝟙 , B)} → canonical tl → canonical tr → canonical {A = A × B} (pair tl tr)
  can-term : {Γ : Con n} → canonical {Γ = Γ} {A = 𝟙} term
  can-abs : {Γ : Con n} {A B : Ty n} {t : Tm (Γ ▹ (𝟙 , A)) (𝟙 , B)} → canonical t → canonical {A = A ⇒ B} (abs (close t))
  can-neu : {Γ : Con n} {x : Fin n} {t : Tm Γ (𝟙 , X x)} → neutral t → canonical {A = X x} t

data neutral {n} where
  neu-var : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A)} → canonical t → (x : (A , B) ∈ Γ) → neutral (t · var x)
  neu-app : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A ⇒ B)} {u : Tm Γ (𝟙 , A)} → neutral t → canonical u → neutral (pair t u · app)
  neu-fst : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · fst)
  neu-snd : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · snd)

-- A variable does not occur as a target of a type
data noTgt {n : ℕ} (x : Fin n) : Ty n → Type where
  no-X : {y : Fin n} → x ≢ y → noTgt x (X y)
  no-𝟙 : noTgt x 𝟙
  no-× : {A B : Ty n} → noTgt x A → noTgt x B → noTgt x (A × B)
  no-⇒ : {A B : Ty n} → noTgt x B → noTgt x (A ⇒ B)

-- A variable is produced by no generator of a context
data noTgtCon {n : ℕ} (x : Fin n) : Con n → Type where
  no-ε : noTgtCon x ε
  no-▹ : {Δ : Con n} {A B : Ty n} → noTgtCon x Δ → noTgt x B → noTgtCon x (Δ ▹ (A , B))

-- A pasting-scheme
data PS {n : ℕ} : (Γ : Con n) (A : Ty n) → Type

-- A variable occurs exactly once as a target of a type, every argument met on the way being a pasting scheme of Γ
data PStgt {n : ℕ} (Γ : Con n) (x : Fin n) : Ty n → Type

-- A variable is produced by exactly one generator of Δ, whose source is a pasting scheme of Γ
data PStgtCon {n : ℕ} (Γ : Con n) (x : Fin n) : Con n → Type

data PS {n} where
  ps-pair : {Γ : Con n} {A B : Ty n} → PS Γ A → PS Γ B → PS Γ (A × B)
  ps-term : {Γ : Con n} → PS Γ 𝟙
  ps-abs : {Γ : Con n} {A B : Ty n} → PS (Γ ▹ (𝟙 , A)) B → PS Γ (A ⇒ B)
  ps-neu : {Γ : Con n} {x : Fin n} → PStgtCon Γ x Γ → PS Γ (X x)

data PStgt {n} Γ x where
  tgt-X : PStgt Γ x (X x)
  tgt-l : {A B : Ty n} → PStgt Γ x A → noTgt x B → PStgt Γ x (A × B)
  tgt-r : {A B : Ty n} → noTgt x A → PStgt Γ x B → PStgt Γ x (A × B)
  tgt-⇒ : {A B : Ty n} → PS Γ A → PStgt Γ x B → PStgt Γ x (A ⇒ B)

data PStgtCon {n} Γ x where
  tgt-here : {Δ : Con n} {A B : Ty n} → noTgtCon x Δ → PS Γ A → PStgt Γ x B → PStgtCon Γ x (Δ ▹ (A , B))
  tgt-drop : {Δ : Con n} {A B : Ty n} → PStgtCon Γ x Δ → noTgt x B → PStgtCon Γ x (Δ ▹ (A , B))

-- The head variable selected by a target occurrence
tgtVar : {n : ℕ} {Γ Δ : Con n} {x : Fin n} → PStgtCon Γ x Δ → Σ[ A ∈ Arr n ] (A ∈ Δ)
tgtVar (tgt-here _ _ _) = _ , here
tgtVar (tgt-drop t _) = _ , drop (proj₂ (tgtVar t))

--- Examples: the pasting schemes postulated in Ty.agda

-- ⊢ X ⇒ X
PS⊢X⇒X' : PS {n = 1} ε (X (# 0) ⇒ X (# 0))
PS⊢X⇒X' = ps-abs (ps-neu (tgt-here no-ε ps-term tgt-X))

-- X ⇒ Y ⊢ X ⇒ Y
PSX⇒Y⊢X⇒Y' : PS {n = 2} (ε ▹ (X (# 0) , X (# 1))) (X (# 0) ⇒ X (# 1))
PSX⇒Y⊢X⇒Y' =
  ps-abs (ps-neu (tgt-drop
    (tgt-here no-ε (ps-neu (tgt-here (no-▹ no-ε (no-X λ ())) ps-term tgt-X)) tgt-X)
    (no-X λ ())))

-- X ⇒ Y , Y ⇒ Z ⊢ X ⇒ Z
PSX⇒Y,Y⇒Z⊢X⇒Z' : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 1) , X (# 2))) (X (# 0) ⇒ X (# 2))
PSX⇒Y,Y⇒Z⊢X⇒Z' = ps-abs (ps-neu ps-Z)
  where
  -- X is produced by the variable bound by the abstraction
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  -- Y is produced by X ⇒ Y, two entries back
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-drop (tgt-here no-ε ps-X tgt-X) (no-X λ ())) (no-X λ ()))
  -- Z is produced by Y ⇒ Z
  ps-Z : PStgtCon _ (# 2) _
  ps-Z = tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-Y tgt-X) (no-X λ ())

-- ⊢ X ⇒ 1
PS⊢X⇒𝟙' : PS {n = 1} ε (X (# 0) ⇒ 𝟙)
PS⊢X⇒𝟙' = ps-abs ps-term

-- ⊢ X × Y ⇒ X   (the projection is forced by tgt-l)
PS⊢X×Y⇒X' : PS {n = 2} ε ((X (# 0) × X (# 1)) ⇒ X (# 0))
PS⊢X×Y⇒X' = ps-abs (ps-neu (tgt-here no-ε ps-term (tgt-l tgt-X (no-X λ ()))))

PS⊢X×Y⇒Y' : PS {n = 2} ε ((X (# 0) × X (# 1)) ⇒ X (# 1))
PS⊢X×Y⇒Y' = ps-abs (ps-neu (tgt-here no-ε ps-term (tgt-r (no-X λ ()) tgt-X)))

PS⊢X×Y⇒X×Y' : PS {n = 2} ε ((X (# 0) × X (# 1)) ⇒ (X (# 0) × X (# 1)))
PS⊢X×Y⇒X×Y' = ps-abs (ps-pair
  (ps-neu (tgt-here no-ε ps-term (tgt-l tgt-X (no-X λ ()))))
  (ps-neu (tgt-here no-ε ps-term (tgt-r (no-X λ ()) tgt-X))))

-- X ⇒ Y , X ⇒ Z ⊢ X ⇒ Y × Z   (X is shared as a *source*, which is allowed)
PSX⇒Y,X⇒Z⊢X⇒Y×Z' : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) ⇒ (X (# 1) × X (# 2)))
PSX⇒Y,X⇒Z⊢X⇒Y×Z' = ps-abs (ps-pair ps-Y ps-Z)
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-drop (tgt-here no-ε ps-X tgt-X) (no-X λ ())) (no-X λ ()))
  ps-Z : PS _ (X (# 2))
  ps-Z = ps-neu (tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-X tgt-X) (no-X λ ()))

-- ⊢ X ⇒ Y ⇒ X : the K combinator, commented out in Ty.agda but a pasting
-- scheme indeed: Y is produced but never demanded, which is harmless
PS⊢X⇒Y⇒X' : PS {n = 2} ε (X (# 0) ⇒ X (# 1) ⇒ X (# 0))
PS⊢X⇒Y⇒X' = ps-abs (ps-abs (ps-neu (tgt-drop (tgt-here no-ε ps-term tgt-X) (no-X λ ()))))

-- ⊢ (X ⇒ Y) ⇒ X ⇒ Y : the only example using tgt-⇒, i.e. an application. Note
-- that noTgt sees X as absent from X ⇒ Y, sources being consumed not produced
PS⊢[X⇒Y]⇒X⇒Y' : PS {n = 2} ε ((X (# 0) ⇒ X (# 1)) ⇒ X (# 0) ⇒ X (# 1))
PS⊢[X⇒Y]⇒X⇒Y' = ps-abs (ps-abs (ps-neu (tgt-drop (tgt-here no-ε ps-term (tgt-⇒ ps-X tgt-X)) (no-X λ ()))))
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ no-ε (no-⇒ (no-X λ ()))) ps-term tgt-X)

-- Demand-driven: X is produced twice here, but never demanded, so this still
-- is a pasting scheme (its unique term being abs term)
PSX⊢X⇒𝟙' : PS {n = 1} (ε ▹ (𝟙 , X (# 0))) (X (# 0) ⇒ 𝟙)
PSX⊢X⇒𝟙' = ps-abs ps-term

-- Non-example: two producers for X, so that the head variable is not
-- determined and both branches of PStgtCon require X ≢ X
¬PSX,X⊢X : ¬ PS {n = 1} (ε ▹ (𝟙 , X (# 0)) ▹ (𝟙 , X (# 0))) (X (# 0))
¬PSX,X⊢X (ps-neu (tgt-here (no-▹ _ (no-X p)) _ _)) = p refl
¬PSX,X⊢X (ps-neu (tgt-drop _ (no-X p))) = p refl
