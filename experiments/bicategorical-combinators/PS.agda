open import Prelude
open import Relation.Nullary using (¬_)
open import Ty
-- open import CC

-- A variable does not occur as a target of a type
data noTgt {n : ℕ} (x : Fin n) : Ty n → Type where
  no-X : {y : Fin n} → x ≢ y → noTgt x (X y)
  no-𝟙 : noTgt x 𝟙
  no-× : {A B : Ty n} → noTgt x A → noTgt x B → noTgt x (A × B)
  no-↝ : {A B : Ty n} → noTgt x B → noTgt x (A ↝ B)

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
  ps-pa   : {Γ : Con n} {A B : Ty n} → PS Γ A → PS Γ B → PS Γ (A × B)
  ps-term : {Γ : Con n} → PS Γ 𝟙
  ps-abs  : {Γ : Con n} {A B : Ty n} → PS (Γ ▹ (𝟙 , A)) B → PS Γ (A ↝ B)
  ps-neu  : {Γ : Con n} {x : Fin n} → PStgtCon Γ x Γ → PS Γ (X x)

data PStgt {n} Γ x where
  tgt-X : PStgt Γ x (X x)
  tgt-l : {A B : Ty n} → PStgt Γ x A → noTgt x B → PStgt Γ x (A × B)
  tgt-r : {A B : Ty n} → noTgt x A → PStgt Γ x B → PStgt Γ x (A × B)
  tgt-↝ : {A B : Ty n} → PS Γ A → PStgt Γ x B → PStgt Γ x (A ↝ B)

data PStgtCon {n} Γ x where
  tgt-here : {Δ : Con n} {A B : Ty n} → noTgtCon x Δ → PS Γ A → PStgt Γ x B → PStgtCon Γ x (Δ ▹ (A , B))
  tgt-drop : {Δ : Con n} {A B : Ty n} → PStgtCon Γ x Δ → noTgt x B → PStgtCon Γ x (Δ ▹ (A , B))

-- A pasting scheme for an arrow: an arrow (A , B) is pasted as the type A ↝ B
PSArr : {n : ℕ} (Γ : Con n) (A : Arr n) → Type
PSArr Γ (A , B) = PS Γ (A ↝ B)

-- The head variable selected by a target occurrence
tgtVar : {n : ℕ} {Γ Δ : Con n} {x : Fin n} → PStgtCon Γ x Δ → Σ[ A ∈ Arr n ] (A ∈ Δ)
tgtVar (tgt-here _ _ _) = _ , here
tgtVar (tgt-drop t _) = _ , drop (proj₂ (tgtVar t))

--- Examples

-- ⊢ X ↝ X
PS⊢X↝X : PS {n = 1} ε (X (# 0) ↝ X (# 0))
PS⊢X↝X = ps-abs (ps-neu (tgt-here no-ε ps-term tgt-X))

-- X ↝ Y ⊢ X ↝ Y
PSX↝Y⊢X↝Y : PS {n = 2} (ε ▹ (X (# 0) , X (# 1))) (X (# 0) ↝ X (# 1))
PSX↝Y⊢X↝Y =
  ps-abs (ps-neu (tgt-drop
    (tgt-here no-ε (ps-neu (tgt-here (no-▹ no-ε (no-X λ ())) ps-term tgt-X)) tgt-X)
    (no-X λ ())))

-- X ↝ Y , Y ↝ Z ⊢ X ↝ Z
PSX↝Y,Y↝Z⊢X↝Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 1) , X (# 2))) (X (# 0) ↝ X (# 2))
PSX↝Y,Y↝Z⊢X↝Z = ps-abs (ps-neu ps-Z)
  where
  -- X is produced by the variable bound by the abstraction
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  -- Y is produced by X ↝ Y, two entries back
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-drop (tgt-here no-ε ps-X tgt-X) (no-X λ ())) (no-X λ ()))
  -- Z is produced by Y ↝ Z
  ps-Z : PStgtCon _ (# 2) _
  ps-Z = tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-Y tgt-X) (no-X λ ())

-- ⊢ X ↝ 1
PS⊢X↝𝟙 : PS {n = 1} ε (X (# 0) ↝ 𝟙)
PS⊢X↝𝟙 = ps-abs ps-term

-- ⊢ X × Y ↝ X   (the projection is forced by tgt-l)
PS⊢X×Y↝X : PS {n = 2} ε ((X (# 0) × X (# 1)) ↝ X (# 0))
PS⊢X×Y↝X = ps-abs (ps-neu (tgt-here no-ε ps-term (tgt-l tgt-X (no-X λ ()))))

PS⊢X×Y↝Y : PS {n = 2} ε ((X (# 0) × X (# 1)) ↝ X (# 1))
PS⊢X×Y↝Y = ps-abs (ps-neu (tgt-here no-ε ps-term (tgt-r (no-X λ ()) tgt-X)))

PS⊢X×Y↝X×Y : PS {n = 2} ε ((X (# 0) × X (# 1)) ↝ (X (# 0) × X (# 1)))
PS⊢X×Y↝X×Y = ps-abs (ps-pa
  (ps-neu (tgt-here no-ε ps-term (tgt-l tgt-X (no-X λ ()))))
  (ps-neu (tgt-here no-ε ps-term (tgt-r (no-X λ ()) tgt-X))))

-- X ↝ Y , X ↝ Z ⊢ X ↝ Y × Z   (X is shared as a *source*, which is allowed)
PSX↝Y,X↝Z⊢X↝Y×Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) ↝ (X (# 1) × X (# 2)))
PSX↝Y,X↝Z⊢X↝Y×Z = ps-abs (ps-pa ps-Y ps-Z)
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-drop (tgt-here no-ε ps-X tgt-X) (no-X λ ())) (no-X λ ()))
  ps-Z : PS _ (X (# 2))
  ps-Z = ps-neu (tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-X tgt-X) (no-X λ ()))

-- X ↝ Y , X ↝ Z ⊢ X ↝ Y   (same as above, keeping only the first component)
PSX↝Y,X↝Z⊢X↝Y : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) ↝ X (# 1))
PSX↝Y,X↝Z⊢X↝Y = ps-abs ps-Y
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-drop (tgt-here no-ε ps-X tgt-X) (no-X λ ())) (no-X λ ()))

-- X ↝ Y , X ↝ Z ⊢ X ↝ Z
PSX↝Y,X↝Z⊢X↝Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) ↝ X (# 2))
PSX↝Y,X↝Z⊢X↝Z = ps-abs ps-Z
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  ps-Z : PS _ (X (# 2))
  ps-Z = ps-neu (tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-X tgt-X) (no-X λ ()))

-- X ↝ 1 ⊢ X ↝ 1   (the generator is never demanded, cf. PSX⊢X↝𝟙 below)
PSX↝1⊢X↝1 : PS {n = 1} (ε ▹ (X (# 0) , 𝟙)) (X (# 0) ↝ 𝟙)
PSX↝1⊢X↝1 = ps-abs ps-term

-- ⊢ X ↝ Y ↝ X : the K combinator: Y is produced but never demanded, which is harmless
PS⊢X↝Y↝X : PS {n = 2} ε (X (# 0) ↝ X (# 1) ↝ X (# 0))
PS⊢X↝Y↝X = ps-abs (ps-abs (ps-neu (tgt-drop (tgt-here no-ε ps-term tgt-X) (no-X λ ()))))

-- ⊢ (X ↝ Y) ↝ X ↝ Y : the only example using tgt-↝, i.e. an application. Note
-- that noTgt sees X as absent from X ↝ Y, sources being consumed not produced
PS⊢[X↝Y]↝X↝Y : PS {n = 2} ε ((X (# 0) ↝ X (# 1)) ↝ X (# 0) ↝ X (# 1))
PS⊢[X↝Y]↝X↝Y = ps-abs (ps-abs (ps-neu (tgt-drop (tgt-here no-ε ps-term (tgt-↝ ps-X tgt-X)) (no-X λ ()))))
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ no-ε (no-↝ (no-X λ ()))) ps-term tgt-X)

-- Demand-driven: X is produced twice here, but never demanded, so this still
-- is a pasting scheme (its unique term being abs term)
PSX⊢X↝𝟙 : PS {n = 1} (ε ▹ (𝟙 , X (# 0))) (X (# 0) ↝ 𝟙)
PSX⊢X↝𝟙 = ps-abs ps-term

-- ⊢ (X ↝ Y) × X ↝ Y : the evaluation map. The single generator produces both
-- Y (through the left component, applied to X) and X (through the right one),
-- which is legitimate since these are two distinct variables
PS⊢[X↝Y]×X↝Y : PS {n = 2} ε ((X (# 0) ↝ X (# 1)) × X (# 0) ↝ X (# 1))
PS⊢[X↝Y]×X↝Y = ps-abs (ps-neu (tgt-here no-ε ps-term (tgt-l (tgt-↝ ps-X tgt-X) (no-X λ ()))))
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here no-ε ps-term (tgt-r (no-↝ (no-X λ ())) tgt-X))

-- X × Y ↝ Z ⊢ X ↝ Y ↝ Z : currying
PSX×Y↝Z⊢X↝Y↝Z : PS {n = 3} (ε ▹ (X (# 0) × X (# 1) , X (# 2))) (X (# 0) ↝ X (# 1) ↝ X (# 2))
PSX×Y↝Z⊢X↝Y↝Z = ps-abs (ps-abs (ps-neu ps-Z))
  where
  -- X and Y are produced by the two variables bound by the abstractions
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-term tgt-X) (no-X λ ()))
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  -- Z is produced by the generator, whose source X × Y is pasted from the two
  ps-Z : PStgtCon _ (# 2) _
  ps-Z = tgt-drop (tgt-drop (tgt-here no-ε (ps-pa ps-X ps-Y) tgt-X) (no-X λ ())) (no-X λ ())

-- X × Y ↝ Z ⊢ X × Y ↝ Z : the same generator, pasted against its own source
PSX×Y↝Z⊢X×Y↝Z : PS {n = 3} (ε ▹ (X (# 0) × X (# 1) , X (# 2))) (X (# 0) × X (# 1) ↝ X (# 2))
PSX×Y↝Z⊢X×Y↝Z = ps-abs (ps-neu ps-Z)
  where
  -- X and Y are the two projections of the variable bound by the abstraction
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ no-ε (no-X λ ())) ps-term (tgt-l tgt-X (no-X λ ())))
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-here (no-▹ no-ε (no-X λ ())) ps-term (tgt-r (no-X λ ()) tgt-X))
  ps-Z : PStgtCon _ (# 2) _
  ps-Z = tgt-drop (tgt-here no-ε (ps-pa ps-X ps-Y) tgt-X) (no-× (no-X λ ()) (no-X λ ()))

-- X ↝ Y ↝ Z ⊢ X ↝ Y ↝ Z : needed for the η-rule of abstraction
PSX↝Y↝Z⊢X↝Y↝Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1) ↝ X (# 2))) (X (# 0) ↝ X (# 1) ↝ X (# 2))
PSX↝Y↝Z⊢X↝Y↝Z = ps-abs (ps-abs (ps-neu ps-Z))
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-drop (tgt-here (no-▹ no-ε (no-↝ (no-X λ ()))) ps-term tgt-X) (no-X λ ()))
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-here (no-▹ (no-▹ no-ε (no-↝ (no-X λ ()))) (no-X λ ())) ps-term tgt-X)
  -- Z is reached by applying the generator (source X) to Y
  ps-Z : PStgtCon _ (# 2) _
  ps-Z = tgt-drop (tgt-drop (tgt-here no-ε ps-X (tgt-↝ ps-Y tgt-X)) (no-X λ ())) (no-X λ ())

-- X ↝ Y × Z ⊢ X ↝ Y × Z : needed for the η-rule of pairing
PSX↝Y×Z⊢X↝Y×Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1) × X (# 2))) (X (# 0) ↝ X (# 1) × X (# 2))
PSX↝Y×Z⊢X↝Y×Z = ps-abs (ps-pa ps-Y ps-Z)
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ no-ε (no-× (no-X λ ()) (no-X λ ()))) ps-term tgt-X)
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-here no-ε ps-X (tgt-l tgt-X (no-X λ ()))) (no-X λ ()))
  ps-Z : PS _ (X (# 2))
  ps-Z = ps-neu (tgt-drop (tgt-here no-ε ps-X (tgt-r (no-X λ ()) tgt-X)) (no-X λ ()))

-- X ↝ Y , Y ↝ Z , Z ↝ W ⊢ X ↝ W : needed for associativity of composition
PSX↝Y,Y↝Z,Z↝W⊢X↝W : PS {n = 4} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 1) , X (# 2)) ▹ (X (# 2) , X (# 3))) (X (# 0) ↝ X (# 3))
PSX↝Y,Y↝Z,Z↝W⊢X↝W = ps-abs (ps-neu ps-W)
  where
  ps-X : PS _ (X (# 0))
  ps-X = ps-neu (tgt-here (no-▹ (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) (no-X λ ())) ps-term tgt-X)
  ps-Y : PS _ (X (# 1))
  ps-Y = ps-neu (tgt-drop (tgt-drop (tgt-drop (tgt-here no-ε ps-X tgt-X) (no-X λ ())) (no-X λ ())) (no-X λ ()))
  ps-Z : PS _ (X (# 2))
  ps-Z = ps-neu (tgt-drop (tgt-drop (tgt-here (no-▹ no-ε (no-X λ ())) ps-Y tgt-X) (no-X λ ())) (no-X λ ()))
  ps-W : PStgtCon _ (# 3) _
  ps-W = tgt-drop (tgt-here (no-▹ (no-▹ no-ε (no-X λ ())) (no-X λ ())) ps-Z tgt-X) (no-X λ ())

-- Non-example: two producers for X, so that the head variable is not
-- determined and both branches of PStgtCon require X ≢ X
¬PSX,X⊢X : ¬ PS {n = 1} (ε ▹ (𝟙 , X (# 0)) ▹ (𝟙 , X (# 0))) (X (# 0))
¬PSX,X⊢X (ps-neu (tgt-here (no-▹ _ (no-X p)) _ _)) = p refl
¬PSX,X⊢X (ps-neu (tgt-drop _ (no-X p))) = p refl
