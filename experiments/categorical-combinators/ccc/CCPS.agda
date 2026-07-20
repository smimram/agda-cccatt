-- Pasting schemes in categorical combinators

open import Prelude
open import Ty
open import PS
open import CC
open import CCNF

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

PSCanEq : {n : ℕ} {Γ : Con n} {A B : Ty n} (ps : PS Γ (A ⇒ B)) {t u : Tm Γ (A , B)} → canonical {!!} → canonical {!!} → t ∼ u
PSCanEq = {!!}
