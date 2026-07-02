-- Our calculus CCaTT

open import Prelude
open import Ty

-- Terms
data Tm {n : ℕ} (Γ : Con n) : (A : Ty n) → Type

-- Substitutions for terms
Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
Sub τ Γ ε = Unit
Sub τ Γ (Γ' ▹ A) = Sub τ Γ Γ' × Tm Γ (A [ τ ]')

data Tm {n} Γ where
  var : {A : Ty n} → A ∈ Γ → Tm Γ A
  coh : {n' : ℕ} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) (τ : SubTy n n') (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]')

Wk : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ A → Tm (Γ ▹ B) A
SubWk : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : Sub τ Γ Γ') (A : Ty n) → Sub τ (Γ ▹ A) Γ'

Wk (var x) = var (drop x)
Wk (coh ps τ σ) = coh ps τ (SubWk σ _)

SubWk {Γ' = ε} tt A = tt
SubWk {Γ' = Γ' ▹ B} (σ , t) A = SubWk σ A , Wk t

-- Identity substitution
SubId : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ Γ
SubId ε = tt
SubId (Γ ▹ A) = SubWk (SubId Γ) A , var here

-- Terminal substitution
SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
SubTerm Γ = tt

-- Application of a substutituion
_[_] : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} → Tm Γ' A → (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]')

-- Same as _[_] but with explicit τ
_[∣_∣_] : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} → Tm Γ' A → (τ : SubTy n n') (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]')
_[∣_∣_] t τ σ = t [ σ ]

-- Composition of substitutions
_∘_ : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {n'' : ℕ} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} →
          Sub τ' Γ' Γ'' → Sub τ Γ Γ' → 
          Sub (τ' ∘' τ) Γ Γ''
_∘_ {Γ'' = ε} σ' σ = tt
_∘_ {Γ'' = Γ'' ▹ A} (σ' , t) σ = σ' ∘ σ , t [ σ ]

-- Functoriality of substitution application
[∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Ty n''} {t : Tm Γ'' A} {τ : SubTy n n'} {σ : Sub τ Γ Γ'} {τ' : SubTy n' n''} {σ' : Sub τ' Γ' Γ''} →
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

I : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (A ⇒ A)
I {n} {Γ} {A} = coh PS⊢X⇒X (SubTy1 A) tt

K : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A)
K {n} {Γ} {A} {B} = coh PS⊢X⇒Y⇒X (SubTy2 A B) tt

S : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm Γ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
S {n} {Γ} {A} {B} {C} = coh PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z (SubTy3 A B C) tt

ap : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
ap {n} {Γ} {A} {B} t u = coh PSX⇒Y,X⊢Y (SubTy2 A B) ((tt , t) , u)

ap2 : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm Γ (A ⇒ B ⇒ C) → Tm Γ A → Tm Γ B → Tm Γ C
ap2 t u v = ap (ap t u) v

ap3 : {n : ℕ} {Γ : Con n} {A B C D : Ty n} → Tm Γ (A ⇒ B ⇒ C ⇒ D) → Tm Γ A → Tm Γ B → Tm Γ C → Tm Γ D
ap3 t u v w = ap (ap2 t u v) w

---
--- Relations
---

-- Applying coh with equal substitutions gives equal terms
coh≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) {τ τ' : SubTy n n'} (p : τ ≡ τ') → {σ : Sub τ Γ Γ'} {σ' : Sub τ' Γ Γ'} → subst (λ τ → Sub τ Γ Γ') p σ ≡ σ' → subst (λ τ → Tm Γ (A [ τ ]')) p (coh ps τ σ) ≡ coh ps τ' σ'
coh≡ ps refl refl = refl

infix 5 _∼_

-- Equivalence of substitutions
_∼Sub_   : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} → Sub τ Γ Γ' → Sub τ Γ Γ' → Type
∼SubRefl : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : Sub τ Γ Γ') → _∼Sub_ {Γ = Γ} σ σ
∼SubSym  : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} {σ σ' : Sub τ Γ Γ'} → _∼Sub_ {Γ = Γ} σ σ' → _∼Sub_ {Γ = Γ} σ' σ

-- Equivalence of terms
data _∼_ {n : ℕ} {Γ : Con n} : {A : Ty n} → Tm Γ A → Tm Γ A → Type where
  eqv : {A : Ty n} (x : A ∈ Γ) → var x ∼ var x
  eq  : {n' : ℕ} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) (t t' : Tm Γ' A) (τ : SubTy n n') {σ σ' : Sub τ Γ Γ'} (p : _∼Sub_ {Γ = Γ} σ σ') → t [ σ ] ∼ t' [ σ' ]
  -- TODO: can this be derived???
  ∼trans : {A : Ty n} {t u v : Tm Γ A} (p : t ∼ u) (q : u ∼ v) → t ∼ v

-- simple variant of eq without ∼ for substitution
eqs : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) (t u : Tm Γ' A) (τ : SubTy n n') (σ : Sub τ Γ Γ') → t [ σ ] ∼ u [ σ ]
eqs ps t u τ σ = eq ps t u τ (∼SubRefl σ)

eqs' : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) (t : Tm Γ' A) (τ : SubTy n n') {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
eqs' ps t τ p = eq ps t t τ p

-- Equivalence of substitutions is reflexive
∼refl : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ A) → t ∼ t
∼refl (var x) = eqv x
∼refl (coh {n'} {Γ'} ps τ σ) = subst₂ _∼_ (cong (coh ps τ) (∘UnitL σ)) (cong (coh ps τ) (∘UnitL σ)) (eq ps (coh ps (SubTyId n') (SubId Γ')) (coh ps (SubTyId n') (SubId Γ')) τ (∼SubRefl σ))

∼of≡ : {n : ℕ} {Γ : Con n} {A : Ty n} {t t' : Tm Γ A} → t ≡ t' → t ∼ t'
∼of≡ refl = ∼refl _

∼sym : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : Tm Γ A} → t ∼ u → u ∼ t
∼sym (eqv x) = eqv x
∼sym (eq ps t u τ p) = eq ps u t τ (∼SubSym p)
∼sym (∼trans p q) = ∼trans (∼sym q) (∼sym p)

-- ∼trans : {n : ℕ} {Γ : Con n} {A : Ty n} {t u v : Tm Γ A} → t ∼ u → u ∼ v → t ∼ v
-- ∼trans (eqv x) q = q
-- ∼trans (eq ps t u τ p) q = {!!}
  -- -- basically, if q is (eqv x), we are as above, and if q is eq then we can use the same eq ps for both => NO!

_∼Sub_ {Γ' = ε} σ σ' = Unit
_∼Sub_ {Γ = Γ} {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (_∼Sub_ {Γ = Γ} σ σ') × t ∼ t'

∼ap : {n : ℕ} {Γ : Con n} {A B : Ty n} {t t' : Tm Γ (A ⇒ B)} {u u' : Tm Γ A} → t ∼ t' → u ∼ u' → ap t u ∼ ap t' u'
∼ap {n} {Γ} {A} {B} p q = eq PSX⇒Y,X⊢Y v v (SubTy2 A B) ((tt , p) , q)
  where
  v : Tm {n = 2} (ε ▹ (X (# 0) ⇒ X (# 1)) ▹ X (# 0)) (X (# 1))
  v = ap (var (drop here)) (var here)

∼SubRefl {Γ' = ε} tt = tt
∼SubRefl {Γ' = Γ' ▹ A} (σ , t) = ∼SubRefl σ , ∼refl t

∼SubSym {Γ' = ε} tt = tt
∼SubSym {Γ' = Γ' ▹ A} (p , q) = ∼SubSym p , ∼sym q

_[_]∼ : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : Tm Γ' A) {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
var here [ p ]∼ = snd p
var (drop x) [ p ]∼ = (var x) [ fst p ]∼
coh ps τ σ [ p ]∼ = {!!} -- equivalent substitutions are closed under left composition

apI : {n : ℕ} {Γ : Con n} {A : Ty n} (t : Tm Γ A) → ap I t ∼ t
apI {n} {Γ} {A} t = eqs PSX⊢X (ap I (var here)) (var here) τ σ
  where
  τ : SubTy n 1
  τ = SubTy1 A
  Γ' : Con 1
  Γ' = ε ▹ X zero
  σ : Sub τ Γ Γ'
  σ = tt , t

apK : {n : ℕ} {Γ : Con n} {A B : Ty n} (t : Tm Γ A) (u : Tm Γ B) → ap (ap K t) u ∼ t
apK {n} {Γ} {A} {B} t u = eqs PSX,Y⊢X (ap (ap K x) y) x (SubTy2 A B) ((tt , t) , u)
  where
  x = var (drop here)
  y = var here

apS : {n : ℕ} {Γ : Con n} {A B C : Ty n} (t : Tm Γ (A ⇒ B ⇒ C)) (u : Tm Γ (A ⇒ B)) (v : Tm Γ A) → ap3 S t u v ∼ ap2 t v (ap u v)
apS {n} {Γ} {A} {B} {C} t u v = eqs PSX⇒Y⇒Z,X⇒Y,X⊢Z (ap3 S x y z) (ap2 x z (ap y z)) (SubTy3 A B C) (((tt , t) , u) , v)
  where
  x = var (drop (drop here))
  y = var (drop here)
  z = var here

lamIβ : {n : ℕ} {Γ : Con n} {A B : Ty n} → _∼_ {Γ = Γ} {A = (A ⇒ B) ⇒ (A ⇒ B)} (ap S (ap K I)) I
lamIβ {n} {Γ} {A} {B} = eqs PS⊢[X⇒Y]⇒X⇒Y (ap S (ap K I)) I (SubTy2 A B) tt

lamKβ : {n : ℕ} {Γ : Con n} {A B C : Ty n} → _∼_ {Γ = Γ} {A = (A ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)} (ap2 S (ap K S) (ap S (ap K K))) K
lamKβ {n} {Γ} {A} {B} {C} = eqs PS⊢[X⇒Z]⇒[X⇒Y]⇒[X⇒Z] (ap2 S (ap K S) (ap S (ap K K))) K (SubTy3 A B C) tt

lamSβ : {n : ℕ} {Γ : Con n} {A B C D : Ty n} → _∼_ {Γ = Γ} {A = (A ⇒ B ⇒ C ⇒ D) ⇒ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ D}
        (ap2 S (ap K (ap S (ap K S))) (ap2 S (ap K S) (ap S (ap K S))))
        (ap2 S (ap2 S (ap K S) (ap2 S (ap K K) (ap2 S (ap K S) (ap2 S (ap K (ap S (ap K S))) S)))) (ap K S))
lamSβ {n} {Γ} {A} {B} {C} {D} = eqs PS⊢[X⇒Y⇒Z⇒W]⇒[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒W (ap2 S (ap K (ap S (ap K S))) (ap2 S (ap K S) (ap S (ap K S)))) (ap2 S (ap2 S (ap K S) (ap2 S (ap K K) (ap2 S (ap K S) (ap2 S (ap K (ap S (ap K S))) S)))) (ap K S)) (SubTy4 A B C D) tt

lamwk : {n : ℕ} {Γ : Con n} {A B C : Ty n} → _∼_ {Γ = Γ} {A = (A ⇒ C) ⇒ A ⇒ B ⇒ C}
        (ap2 S (ap2 S (ap K S) (ap2 S (ap K K) (ap2 S (ap K S) K))) (ap K K))
        (ap S (ap K K))
lamwk {n} {Γ} {A} {B} {C} = eqs PS⊢[X⇒Z]⇒X⇒Y⇒Z (ap2 S (ap2 S (ap K S) (ap2 S (ap K K) (ap2 S (ap K S) K))) (ap K K)) (ap S (ap K K)) (SubTy3 A B C) tt

lamη : {n : ℕ} {Γ : Con n} {A B : Ty n} → _∼_ {Γ = Γ} {A = (A ⇒ B) ⇒ A ⇒ B} (ap2 S (ap2 S (ap K S) K) (ap K I)) I
lamη {n} {Γ} {A} {B} = eqs PS⊢[X⇒Y]⇒X⇒Y (ap2 S (ap2 S (ap K S) K) (ap K I)) I (SubTy2 A B) tt
