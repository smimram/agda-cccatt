-- Our calculus CCaTT

open import Prelude
open import Ty

-- Terms
data Tm {n : ℕ} (Γ : Con n) : (A : Arr n) → Type

-- Substitutions for terms
Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
Sub τ Γ ε = Unit
Sub τ Γ (Γ' ▹ (A , B)) = Sub τ Γ Γ' ∧ Tm Γ (A [ τ ]' , B [ τ ]')

data Tm {n} Γ where
  var : {A : Arr n} → A ∈ Γ → Tm Γ A
  coh : {n' : ℕ} {Γ' : Con n'} {A B : Ty n'} (ps : PS Γ' (A , B)) (τ : SubTy n n') (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]' , B [ τ ]')

Wk : {n : ℕ} {Γ : Con n} {A B : Arr n} → Tm Γ A → Tm (Γ ▹ B) A
SubWk : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : Sub τ Γ Γ') (A : Arr n) → Sub τ (Γ ▹ A) Γ'

Wk (var x) = var (drop x)
Wk (coh ps τ σ) = coh ps τ (SubWk σ _)

SubWk {Γ' = ε} σ A = tt
SubWk {Γ' = Γ' ▹ B} (σ , t) A = SubWk σ A , Wk t

-- Identity substitution
SubId : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ Γ
SubId ε = tt
SubId (Γ ▹ A) = SubWk (SubId Γ) A , var here

-- Terminal substitution
SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
SubTerm Γ = tt

-- Application of a substutituion
_[_] : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} {A B : Ty n'} → Tm Γ' (A , B) → (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]' , B [ τ ]')

-- Same as _[_] but with explicit τ
_[∣_∣_] : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A B : Ty n'} → Tm Γ' (A , B) → (τ : SubTy n n') (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]' , B [ τ ]')
_[∣_∣_] t τ σ = t [ σ ]

-- Composition of substitutions
_∘_ : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {n'' : ℕ} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} →
          Sub τ' Γ' Γ'' → Sub τ Γ Γ' → 
          Sub (τ' ∘' τ) Γ Γ''
_∘_ {Γ'' = ε} σ' σ = tt
_∘_ {Γ'' = Γ'' ▹ A} (σ' , t) σ = σ' ∘ σ , t [ σ ]

-- Functoriality of substitution application
[∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Arr n''} {t : Tm Γ'' A} {τ : SubTy n n'} {σ : Sub τ Γ Γ'} {τ' : SubTy n' n''} {σ' : Sub τ' Γ' Γ''} →
      (t [ σ' ] [ σ ]) ≡ t [ σ' ∘ σ ]
[∘] = {!!} -- this is standard material

var here [ σ , t ] = t
var (drop x) [ σ , t ] = var x [ σ ]
_[_] {τ = τ} {Γ = Γ} (coh {A = A} ps τ' σ') σ = coh ps (τ' ∘' τ) (σ' ∘ σ)

-- Unitality of substitutions
∘UnitL : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ : Sub τ Γ Γ') → _∘_ {Γ = Γ} (SubId Γ') σ ≡ σ
∘UnitL {Γ' = ε} tt = refl
∘UnitL {Γ' = Γ' ▹ A} (σ , t) = Σ-≡,≡→≡ ({!!} , {!substConst _ _!}) -- this is standard material

---
--- Deriving basic operations
---

id : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (A , A)
id {n} {Γ} {A} = coh PS⊢X⇒X (SubTy1 A) tt

comp : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
comp {A = A} {B} {C} f g = coh PSX⇒Y,Y⇒Z⊢X⇒Z (SubTy3 A B C) ((tt , f) , g)

infixl 6 _·_
_·_ = comp

term : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (A , 𝟙)
term = coh PS⊢X⇒1 (SubTy1 _) tt

fst : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A × B , A)
fst = coh PS⊢X×Y⇒X (SubTy2 _ _) tt

snd : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A × B , B)
snd = coh PS⊢X×Y⇒Y (SubTy2 _ _) tt

pair : {n : ℕ} {Γ : Con n} {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
pair f g = coh PSX⇒Y,X⇒Z⊢X⇒Y×Z (SubTy3 _ _ _) ((tt , f) , g)

---
--- Relations
---

-- Applying coh with equal substitutions gives equal terms
coh≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A B : Ty n'} (ps : PS Γ' (A , B)) {τ τ' : SubTy n n'} (p : τ ≡ τ') → {σ : Sub τ Γ Γ'} {σ' : Sub τ' Γ Γ'} → subst (λ τ → Sub τ Γ Γ') p σ ≡ σ' → subst (λ τ → Tm Γ (A [ τ ]' , B [ τ ]')) p (coh ps τ σ) ≡ coh ps τ' σ'
coh≡ ps refl refl = refl

infix 5 _∼_

-- Equivalence of substitutions
_∼Sub_   : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} → Sub τ Γ Γ' → Sub τ Γ Γ' → Type
∼SubRefl : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : Sub τ Γ Γ') → _∼Sub_ {Γ = Γ} σ σ
∼SubSym  : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} {σ σ' : Sub τ Γ Γ'} → _∼Sub_ {Γ = Γ} σ σ' → _∼Sub_ {Γ = Γ} σ' σ

-- Equivalence of terms
data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  eqv : {A : Arr n} (x : A ∈ Γ) → var x ∼ var x
  eq  : {n' : ℕ} {Γ' : Con n'} {A : Arr n'} (ps : PS Γ' A) (t t' : Tm Γ' A) (τ : SubTy n n') {σ σ' : Sub τ Γ Γ'} (p : _∼Sub_ {Γ = Γ} σ σ') → t [ σ ] ∼ t' [ σ' ]
  -- TODO: can this be derived???
  ∼trans : {A : Arr n} {t u v : Tm Γ A} (p : t ∼ u) (q : u ∼ v) → t ∼ v

-- simple variant of eq without ∼ for substitution
eqs : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (ps : PS Γ' A) (t u : Tm Γ' A) (τ : SubTy n n') (σ : Sub τ Γ Γ') → t [ σ ] ∼ u [ σ ]
eqs ps t u τ σ = eq ps t u τ (∼SubRefl σ)

eqs' : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (ps : PS Γ' A) (t : Tm Γ' A) (τ : SubTy n n') {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
eqs' ps t τ p = eq ps t t τ p

-- Equivalence of substitutions is reflexive
∼refl : {n : ℕ} {Γ : Con n} {A : Arr n} (t : Tm Γ A) → t ∼ t
∼refl (var x) = eqv x
∼refl (coh {n'} {Γ'} ps τ σ) = subst₂ _∼_ (cong (coh ps τ) (∘UnitL σ)) (cong (coh ps τ) (∘UnitL σ)) (eq ps (coh ps (SubTyId n') (SubId Γ')) (coh ps (SubTyId n') (SubId Γ')) τ (∼SubRefl σ))

∼of≡ : {n : ℕ} {Γ : Con n} {A : Arr n} {t t' : Tm Γ A} → t ≡ t' → t ∼ t'
∼of≡ refl = ∼refl _

∼sym : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : Tm Γ A} → t ∼ u → u ∼ t
∼sym (eqv x) = eqv x
∼sym (eq ps t u τ p) = eq ps u t τ (∼SubSym p)
∼sym (∼trans p q) = ∼trans (∼sym q) (∼sym p)

_∼Sub_ {Γ' = ε} σ σ' = Unit
_∼Sub_ {Γ = Γ} {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (_∼Sub_ {Γ = Γ} σ σ') ∧ t ∼ t'

-- ∼ap : {n : ℕ} {Γ : Con n} {A B : Ty n} {t t' : Tm Γ (A ⇒ B)} {u u' : Tm Γ A} → t ∼ t' → u ∼ u' → ap t u ∼ ap t' u'
-- ∼ap {n} {Γ} {A} {B} p q = eq PSX⇒Y,X⊢Y v v (SubTy2 A B) ((tt , p) , q)
  -- where
  -- v : Tm {n = 2} (ε ▹ (X (# 0) ⇒ X (# 1)) ▹ X (# 0)) (X (# 1))
  -- v = ap (var (drop here)) (var here)

∼SubRefl {Γ' = ε} tt = tt
∼SubRefl {Γ' = Γ' ▹ A} (σ , t) = ∼SubRefl σ , ∼refl t

∼SubSym {Γ' = ε} tt = tt
∼SubSym {Γ' = Γ' ▹ A} (p , q) = ∼SubSym p , ∼sym q

_[_]∼ : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : Tm Γ' A) {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
var here [ p , q ]∼ = q
var (drop x) [ p , q ]∼ = (var x) [ p ]∼
coh ps τ σ [ p ]∼ = {!!} -- equivalent substitutions are closed under left composition

---
--- Deriving basic relations
---

unitl : {n : ℕ} {Γ : Con n} {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
unitl f = eqs PSX⇒Y⊢X⇒Y (id · var here) (var here) (SubTy2 _ _) (tt , f)

unitr : {n : ℕ} {Γ : Con n} {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
unitr f = eqs PSX⇒Y⊢X⇒Y (var here · id) (var here) (SubTy2 _ _) (tt , f)

pfst : {n : ℕ} {Γ : Con n} {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · fst ∼ f
pfst f g = eqs PSX⇒Y,X⇒Z⊢X⇒Y (pair (var (drop here)) (var here) · fst) (var (drop here)) (SubTy3 _ _ _) ((tt , f) , g)

psnd : {n : ℕ} {Γ : Con n} {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · snd ∼ g
psnd f g = eqs PSX⇒Y,X⇒Z⊢X⇒Z (pair (var (drop here)) (var here) · snd) (var here) (SubTy3 _ _ _) ((tt , f) , g)

pext : {n : ℕ} {Γ : Con n} {A B : Ty n} → pair fst snd ∼ id {Γ = Γ} {A = A × B}
pext = eqs PS⊢X×Y⇒X×Y (pair fst snd) id (SubTy2 _ _) tt

text : {n : ℕ} {Γ : Con n} {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
text f = eqs PSX⇒1⊢X⇒1 (var here) term (SubTy1 _) (tt , f)
