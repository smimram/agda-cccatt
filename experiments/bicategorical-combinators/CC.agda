--- Cartesian closed categories
--- see for instance Lambek and Scott p.52

open import Prelude
open import Ty
open import PS
open import CCBase public

-- Substitutions
Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
Sub _ Γ ε = Unit
Sub τ Γ (Γ' ▹ (A , B)) = Sub τ Γ Γ' ∧ Tm Γ (A [ τ ]' , B [ τ ]')

-- Terminal substitution
SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
SubTerm Γ = tt

-- Application of a substitution
_[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A B : Ty n'} → Tm Γ' (A , B) → {τ : SubTy n n'} (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]' , B [ τ ]')
var here [ σ , t ] = t
var (drop x) [ σ , t ] = var x [ σ ]
id [ σ ] = id
(f · g) [ σ ] = f [ σ ] · g [ σ ]
term [ σ ] = term
pa f g [ σ ] = pa (f [ σ ]) (g [ σ ])
fst [ σ ] = fst
snd [ σ ] = snd
abs t [ σ ] = abs (t [ σ ])
app [ σ ] = app

-- Equivalence of substitutions
_⇒Sub_ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ σ' : Sub τ Γ Γ') → Type
_⇒Sub_ {Γ' = ε} tt tt = Unit
_⇒Sub_ {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (σ ⇒Sub σ') ∧ (t ⇒ t')

⇒SubRefl : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ : Sub τ Γ Γ') → σ ⇒Sub σ
⇒SubRefl {Γ' = ε} σ = tt
⇒SubRefl {Γ' = Γ' ▹ A} (σ , t) = ⇒SubRefl σ , ⇒refl

⇒SubSym : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ⇒Sub σ' → σ' ⇒Sub σ
⇒SubSym {Γ' = ε} tt = tt
⇒SubSym {Γ' = Γ' ▹ A} (p , q) = ⇒SubSym p , ⇒sym q

-- Applying equivalent substitutions to a term gives equivalent results
-- (recursion on the term, so that _[_]⇒ below can recurse on the proof)
[]⇒ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ⇒Sub σ' → t [ σ ] ⇒ t [ σ' ]
[]⇒ (var here) (σ , p) = p
[]⇒ (var (drop x)) (σ , p) = []⇒ (var x) σ
[]⇒ id p = ⇒refl
[]⇒ (f · g) p = ⇒· ([]⇒ f p) ([]⇒ g p)
[]⇒ term p = ⇒refl
[]⇒ (pa f g) p = ⇒pa ([]⇒ f p) ([]⇒ g p)
[]⇒ fst p = ⇒refl
[]⇒ snd p = ⇒refl
[]⇒ (abs t) p = ⇒abs ([]⇒ t p)
[]⇒ app p = ⇒refl

_[_]⇒ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ⇒ u → σ ⇒Sub σ' → t [ σ ] ⇒ u [ σ' ]
pa-fst f g [ q ]⇒ = ⇒trans (pa-fst (f [ _ ]) (g [ _ ])) ([]⇒ f q)
pa-snd f g [ q ]⇒ = ⇒trans (pa-snd (f [ _ ]) (g [ _ ])) ([]⇒ g q)
pa-eta f [ q ]⇒ = ⇒trans ([]⇒ f q) (pa-eta (f [ _ ]))
term-can f [ q ]⇒ = term-can (f [ _ ])
eps f [ q ]⇒ = ⇒trans (eps (f [ _ ])) ([]⇒ f q)
eta f [ q ]⇒ = ⇒trans ([]⇒ f q) (eta (f [ _ ]))
unitl f [ q ]⇒ = ⇒trans (unitl (f [ _ ])) ([]⇒ f q)
unitr f [ q ]⇒ = ⇒trans (unitr (f [ _ ])) ([]⇒ f q)
assoc f g h [ q ]⇒ = ⇒trans (assoc (f [ _ ]) (g [ _ ]) (h [ _ ])) (⇒· ([]⇒ f q) (⇒· ([]⇒ g q) ([]⇒ h q)))
⇒· p p' [ q ]⇒ = ⇒· (p [ q ]⇒) (p' [ q ]⇒)
⇒pa p p' [ q ]⇒ = ⇒pa (p [ q ]⇒) (p' [ q ]⇒)
⇒abs p [ q ]⇒ = ⇒abs (p [ q ]⇒)
⇒refl {f = f} [ q ]⇒ = []⇒ f q
⇒sym p [ q ]⇒ = ⇒sym (p [ ⇒SubSym q ]⇒)
⇒trans p p' [ q ]⇒ = ⇒trans (p [ q ]⇒) (p' [ ⇒SubRefl _ ]⇒)

-- Composition of substitutions
_∘_ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} → Sub τ' Γ' Γ'' → Sub τ Γ Γ' → Sub (τ' ∘' τ) Γ Γ''
_∘_ {Γ'' = ε} σ' σ = tt
_∘_ {Γ'' = Γ'' ▹ A} (σ' , t') σ = (σ' ∘ σ) , (t' [ σ ])

-- Functoriality of substitution application
[∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Arr n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (t : Tm Γ'' A) (σ' : Sub τ' Γ' Γ'') (σ : Sub τ Γ Γ') → t [ σ' ] [ σ ] ≡ t [ σ' ∘ σ ]
[∘] (var here) (σ' , f) σ = refl
[∘] (var (drop x)) (σ' , f) σ = [∘] (var x) σ' σ
[∘] id σ' σ = refl
[∘] (f · g) σ' σ = cong₂ _·_ ([∘] f σ' σ) ([∘] g σ' σ)
[∘] term σ' σ = refl
[∘] (pa f g) σ' σ = cong₂ pa ([∘] f σ' σ) ([∘] g σ' σ)
[∘] fst σ' σ = refl
[∘] snd σ' σ = refl
[∘] (abs t) σ' σ = cong abs ([∘] t σ' σ)
[∘] app σ' σ = refl

---
--- Currying
---

-- Currying against the terminal source, which brings a term with source A back
-- to a term with source 𝟙
curry : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → Tm Γ (𝟙 , A ↝ B)
curry t = abs (snd · t)

-- ... and its inverse
uncurry : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (𝟙 , A ↝ B) → Tm Γ (A , B)
uncurry t = pa (term · t) id · app

---
--- Normal forms
---

-- Bind the last variable of the context
close : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm (Γ ▹ (𝟙 , A)) (B , C) → Tm Γ (B × A , C)
close (var here) = snd
close (var (drop x)) = fst · var x
close id = fst
close (f · g) = pa (close f) snd · close g
close term = term
close (pa f g) = pa (close f) (close g)
close fst = fst · fst
close snd = fst · snd
close (abs t) = abs (pa (pa (fst · fst) snd) (fst · snd) · close t)
close app = fst · app

-- NOTE: we could extend neutral terms to have A as source instead of 𝟙. However, the PS condition would be more difficult to formulate because we can look up stuff both in the context and in the source.

-- Canonical terms: in βη-long form
data canonical {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type
-- Neutral terms
data neutral {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type

data canonical {n} where
  can-pa : {Γ : Con n} {A B : Ty n} {tl : Tm Γ (𝟙 , A)} {tr : Tm Γ (𝟙 , B)} → canonical tl → canonical tr → canonical {A = A × B} (pa tl tr)
  can-term : {Γ : Con n} → canonical {Γ = Γ} {A = 𝟙} term
  can-abs : {Γ : Con n} {A B : Ty n} {t : Tm (Γ ▹ (𝟙 , A)) (𝟙 , B)} → canonical t → canonical {A = A ↝ B} (abs (close t))
  can-neu : {Γ : Con n} {x : Fin n} {t : Tm Γ (𝟙 , X x)} → neutral t → canonical {A = X x} t

data neutral {n} where
  neu-var : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A)} → canonical t → (x : (A , B) ∈ Γ) → neutral (t · var x)
  neu-app : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A ↝ B)} {u : Tm Γ (𝟙 , A)} → neutral t → canonical u → neutral (pa t u · app)
  neu-fst : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · fst)
  neu-snd : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · snd)
