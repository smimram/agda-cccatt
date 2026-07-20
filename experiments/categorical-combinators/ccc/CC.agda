--- Cartesian closed categories
--- see for instance Lambek and Scott p.52

open import Prelude
open import Data.Empty using (⊥ ; ⊥-elim)
open import Ty
open import PS

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var  : {A : Arr n} → A ∈ Γ → Tm Γ A
  id   : {A : Ty n} → Tm Γ (A , A)
  _·_  : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pair : {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
  fst  : {A B : Ty n} → Tm Γ (A × B , A)
  snd  : {A B : Ty n} → Tm Γ (A × B , B)
  abs  : {A B C : Ty n} → Tm Γ (A × B , C) → Tm Γ (A , B ⇒ C)
  app  : {A B : Ty n} → Tm Γ ((A ⇒ B) × A , B)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  pfst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · fst ∼ f
  psnd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · snd ∼ g
  pext : {A B C : Ty n} (f : Tm Γ (A , B × C)) → f ∼ pair (f · fst) (f · snd)
  text : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
  aβ : {A B C : Ty n} (f : Tm Γ (A × B , C)) → pair (fst · abs f) snd · app ∼ f
  aext : {A B C : Ty n} (f : Tm Γ (A , B ⇒ C)) → f ∼ abs (pair (fst · f) snd · app)
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  ∼· : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼pair : {X A B : Ty n} {f f' : Tm Γ (X , A)} {g g' : Tm Γ (X , B)} → f ∼ f' → g ∼ g' → pair f g ∼ pair f' g'
  ∼abs : {A B C : Ty n} {f f' : Tm Γ (A × B , C)} → f ∼ f' → abs f ∼ abs f'
  ∼refl : {A : Arr n} {f : Tm Γ A} → f ∼ f
  ∼sym  : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h

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
pair f g [ σ ] = pair (f [ σ ]) (g [ σ ])
fst [ σ ] = fst
snd [ σ ] = snd
abs t [ σ ] = abs (t [ σ ])
app [ σ ] = app

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

-- Applying equivalent substitutions to a term gives equivalent results
-- (recursion on the term, so that _[_]∼ below can recurse on the proof)
[]∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
[]∼ (var here) (σ , p) = p
[]∼ (var (drop x)) (σ , p) = []∼ (var x) σ
[]∼ id p = ∼refl
[]∼ (f · g) p = ∼· ([]∼ f p) ([]∼ g p)
[]∼ term p = ∼refl
[]∼ (pair f g) p = ∼pair ([]∼ f p) ([]∼ g p)
[]∼ fst p = ∼refl
[]∼ snd p = ∼refl
[]∼ (abs t) p = ∼abs ([]∼ t p)
[]∼ app p = ∼refl

_[_]∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ∼ u → σ ∼Sub σ' → t [ σ ] ∼ u [ σ' ]
pfst f g [ q ]∼ = ∼trans (pfst (f [ _ ]) (g [ _ ])) ([]∼ f q)
psnd f g [ q ]∼ = ∼trans (psnd (f [ _ ]) (g [ _ ])) ([]∼ g q)
pext f [ q ]∼ = ∼trans ([]∼ f q) (pext (f [ _ ]))
text f [ q ]∼ = text (f [ _ ])
aβ f [ q ]∼ = ∼trans (aβ (f [ _ ])) ([]∼ f q)
aext f [ q ]∼ = ∼trans ([]∼ f q) (aext (f [ _ ]))
unitl f [ q ]∼ = ∼trans (unitl (f [ _ ])) ([]∼ f q)
unitr f [ q ]∼ = ∼trans (unitr (f [ _ ])) ([]∼ f q)
assoc f g h [ q ]∼ = ∼trans (assoc (f [ _ ]) (g [ _ ]) (h [ _ ])) (∼· ([]∼ f q) (∼· ([]∼ g q) ([]∼ h q)))
∼· p p' [ q ]∼ = ∼· (p [ q ]∼) (p' [ q ]∼)
∼pair p p' [ q ]∼ = ∼pair (p [ q ]∼) (p' [ q ]∼)
∼abs p [ q ]∼ = ∼abs (p [ q ]∼)
∼refl {f = f} [ q ]∼ = []∼ f q
∼sym p [ q ]∼ = ∼sym (p [ ∼SubSym q ]∼)
∼trans p p' [ q ]∼ = ∼trans (p [ q ]∼) (p' [ ∼SubRefl _ ]∼)

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
[∘] (pair f g) σ' σ = cong₂ pair ([∘] f σ' σ) ([∘] g σ' σ)
[∘] fst σ' σ = refl
[∘] snd σ' σ = refl
[∘] (abs t) σ' σ = cong abs ([∘] t σ' σ)
[∘] app σ' σ = refl













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

-- postulate
  -- nf : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (𝟙 , A) → Tm Γ (𝟙 , A)
  -- nf∼ : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → t ∼ nf t
  -- nfCan : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → canonical (nf t)


-- Every pasting scheme has a canonical term (the existence half of
-- contractibility): the grammar of PS mirrors the one of canonical terms. The
-- term and the proof that it is canonical are built separately, so that the
-- uniqueness proofs below do not have to carry the (term-irrelevant) canonicity
-- witnesses around.
PSTmTm : {n : ℕ} {Γ : Con n} {A : Ty n} → PS Γ A → Tm Γ (𝟙 , A)
-- A target occurrence tells how to project a neutral term down to X x
PSTgtTm : {n : ℕ} {Γ : Con n} {x : Fin n} {B : Ty n} → PStgt Γ x B → Tm Γ (𝟙 , B) → Tm Γ (𝟙 , X x)
-- Δ is a prefix of the ambient context Γ, whence the inclusion of variables
PSTgtConTm : {n : ℕ} {Γ Δ : Con n} {x : Fin n} → PStgtCon Γ x Δ → ({A : Arr n} → A ∈ Δ → A ∈ Γ) → Tm Γ (𝟙 , X x)

PSTmTm (ps-pair p q) = pair (PSTmTm p) (PSTmTm q)
PSTmTm ps-term = term
PSTmTm (ps-abs p) = abs (close (PSTmTm p))
PSTmTm (ps-neu p) = PSTgtConTm p (λ i → i)

PSTgtTm tgt-X t = t
PSTgtTm (tgt-l p _) t = PSTgtTm p (t · fst)
PSTgtTm (tgt-r _ p) t = PSTgtTm p (t · snd)
PSTgtTm (tgt-⇒ a p) t = PSTgtTm p (pair t (PSTmTm a) · app)

PSTgtConTm (tgt-here _ a p) incl = PSTgtTm p (PSTmTm a · var (incl here))
PSTgtConTm (tgt-drop p _) incl = PSTgtConTm p (λ i → incl (drop i))

-- ... and this term is indeed canonical
PSTmCan : {n : ℕ} {Γ : Con n} {A : Ty n} (p : PS Γ A) → canonical (PSTmTm p)
PSTgtNeu : {n : ℕ} {Γ : Con n} {x : Fin n} {B : Ty n} (p : PStgt Γ x B) {t : Tm Γ (𝟙 , B)} → neutral t → neutral (PSTgtTm p t)
PSTgtConNeu : {n : ℕ} {Γ Δ : Con n} {x : Fin n} (p : PStgtCon Γ x Δ) (incl : {A : Arr n} → A ∈ Δ → A ∈ Γ) → neutral (PSTgtConTm p incl)

PSTmCan (ps-pair p q) = can-pair (PSTmCan p) (PSTmCan q)
PSTmCan ps-term = can-term
PSTmCan (ps-abs p) = can-abs (PSTmCan p)
PSTmCan (ps-neu p) = can-neu (PSTgtConNeu p (λ i → i))

PSTgtNeu tgt-X nt = nt
PSTgtNeu (tgt-l p _) nt = PSTgtNeu p (neu-fst nt)
PSTgtNeu (tgt-r _ p) nt = PSTgtNeu p (neu-snd nt)
PSTgtNeu (tgt-⇒ a p) nt = PSTgtNeu p (neu-app nt (PSTmCan a))

PSTgtConNeu (tgt-here _ a p) incl = PSTgtNeu p (neu-var (PSTmCan a) (incl here))
PSTgtConNeu (tgt-drop p _) incl = PSTgtConNeu p (λ i → incl (drop i))

PSTm' : {n : ℕ} {Γ : Con n} {A : Ty n} → PS Γ A → Σ (Tm Γ (𝟙 , A)) canonical
PSTm' p = PSTmTm p , PSTmCan p

-- In a pasting scheme, there exists a term (with any source)
PSTm : {n : ℕ} {Γ : Con n} {A B : Ty n} → PS Γ B → Tm Γ (A , B)
PSTm p = term · PSTmTm p

--- Uniqueness of the canonical term of a pasting scheme

≡→∼ : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : Tm Γ A} → t ≡ u → t ∼ u
≡→∼ refl = ∼refl

-- The spine of eliminations of a neutral term, in the same order as PStgt (the
-- head of the spine is the elimination applied first), but with the PS
-- conditions forgotten: only the arguments of the applications are retained.
-- This is the accumulator allowing to invert a neutral term, whose derivation
-- proceeds in the opposite order (the outermost elimination first).
data RTgt {n : ℕ} (Γ : Con n) (x : Fin n) : Ty n → Type where
  rtgt-X : RTgt Γ x (X x)
  rtgt-l : {A B : Ty n} → RTgt Γ x A → RTgt Γ x (A × B)
  rtgt-r : {A B : Ty n} → RTgt Γ x B → RTgt Γ x (A × B)
  rtgt-⇒ : {A B : Ty n} (u : Tm Γ (𝟙 , A)) → canonical u → RTgt Γ x B → RTgt Γ x (A ⇒ B)

-- Application of a spine, mirroring PSTgtTm
RTm : {n : ℕ} {Γ : Con n} {x : Fin n} {B : Ty n} → RTgt Γ x B → Tm Γ (𝟙 , B) → Tm Γ (𝟙 , X x)
RTm rtgt-X t = t
RTm (rtgt-l k) t = RTm k (t · fst)
RTm (rtgt-r k) t = RTm k (t · snd)
RTm (rtgt-⇒ u _ k) t = RTm k (pair t u · app)

-- A variable which is not a target cannot be reached by a spine: this is what
-- turns the "exactly one producer" conditions of PS into the determinism of the
-- head variable and of the projections
noTgt-RTgt : {n : ℕ} {Γ : Con n} {x : Fin n} {A : Ty n} → noTgt x A → RTgt Γ x A → ⊥
noTgt-RTgt (no-X p) rtgt-X = p refl
noTgt-RTgt (no-× n _) (rtgt-l k) = noTgt-RTgt n k
noTgt-RTgt (no-× _ n) (rtgt-r k) = noTgt-RTgt n k
noTgt-RTgt (no-⇒ n) (rtgt-⇒ _ _ k) = noTgt-RTgt n k

noTgtCon-RTgt : {n : ℕ} {Γ Δ : Con n} {x : Fin n} {A B : Ty n} → noTgtCon x Δ → (A , B) ∈ Δ → RTgt Γ x B → ⊥
noTgtCon-RTgt (no-▹ _ n) here k = noTgt-RTgt n k
noTgtCon-RTgt (no-▹ n _) (drop y) k = noTgtCon-RTgt n y k

-- A canonical term of a pasting scheme is the one produced by PSTmTm (the
-- uniqueness half of contractibility)
CanUniq : {n : ℕ} {Γ : Con n} {A : Ty n} (ps : PS Γ A) {t : Tm Γ (𝟙 , A)} → canonical t → t ≡ PSTmTm ps
-- A neutral term, whose eliminations have been accumulated in a spine k, is the
-- one produced by the (unique) target occurrence p
NeuUniq : {n : ℕ} {Γ : Con n} {x : Fin n} {C : Ty n} (p : PStgtCon Γ x Γ) (k : RTgt Γ x C) {t : Tm Γ (𝟙 , C)} → neutral t → RTm k t ≡ PSTgtConTm p (λ i → i)
-- The head variable of a neutral term is the one selected by p, and its spine
-- is the one described by p
TgtConUniq : {n : ℕ} {Γ Δ : Con n} {x : Fin n} {A B : Ty n} (p : PStgtCon Γ x Δ) (incl : {A : Arr n} → A ∈ Δ → A ∈ Γ) (y : (A , B) ∈ Δ) (k : RTgt Γ x B) {t : Tm Γ (𝟙 , A)} → canonical t → RTm k (t · var (incl y)) ≡ PSTgtConTm p incl
-- A spine reaching x in a type where x occurs exactly once as a target is the
-- expected one
TgtUniq : {n : ℕ} {Γ : Con n} {x : Fin n} {B : Ty n} (q : PStgt Γ x B) (k : RTgt Γ x B) (t : Tm Γ (𝟙 , B)) → RTm k t ≡ PSTgtTm q t

CanUniq (ps-pair p q) (can-pair ct cu) = cong₂ pair (CanUniq p ct) (CanUniq q cu)
CanUniq ps-term can-term = refl
CanUniq (ps-abs p) (can-abs ct) = cong (λ t → abs (close t)) (CanUniq p ct)
CanUniq (ps-neu p) (can-neu nt) = NeuUniq p rtgt-X nt

NeuUniq p k (neu-var ct y) = TgtConUniq p (λ i → i) y k ct
NeuUniq p k (neu-app nt cu) = NeuUniq p (rtgt-⇒ _ cu k) nt
NeuUniq p k (neu-fst nt) = NeuUniq p (rtgt-l k) nt
NeuUniq p k (neu-snd nt) = NeuUniq p (rtgt-r k) nt

TgtConUniq (tgt-here _ a q) incl here k ct = TgtUniq q k _ ∙ cong (λ t → PSTgtTm q (t · var (incl here))) (CanUniq a ct)
TgtConUniq (tgt-here n _ _) _ (drop y) k _ = ⊥-elim (noTgtCon-RTgt n y k)
TgtConUniq (tgt-drop _ n) _ here k _ = ⊥-elim (noTgt-RTgt n k)
TgtConUniq (tgt-drop p _) incl (drop y) k ct = TgtConUniq p (λ i → incl (drop i)) y k ct

TgtUniq tgt-X rtgt-X t = refl
TgtUniq (tgt-l q _) (rtgt-l k) t = TgtUniq q k (t · fst)
TgtUniq (tgt-l _ n) (rtgt-r k) t = ⊥-elim (noTgt-RTgt n k)
TgtUniq (tgt-r n _) (rtgt-l k) t = ⊥-elim (noTgt-RTgt n k)
TgtUniq (tgt-r _ q) (rtgt-r k) t = TgtUniq q k (t · snd)
TgtUniq (tgt-⇒ a q) (rtgt-⇒ u cu k) t = TgtUniq q k _ ∙ cong (λ v → PSTgtTm q (pair t v · app)) (CanUniq a cu)

PSCanEq' : {n : ℕ} {Γ : Con n} {A : Ty n} (ps : PS Γ A) {t u : Tm Γ (𝟙 , A)} → canonical t → canonical u → t ∼ u
PSCanEq' ps ct cu = ≡→∼ (CanUniq ps ct ∙ sym (CanUniq ps cu))
