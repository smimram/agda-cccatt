--- Categorical combinators for cartesian categories

open import Prelude
open import Ty
open import PS

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var : {A : Arr n} → A ∈ Γ → Tm Γ A
  id  : {A : Ty n} → Tm Γ (A , A)
  _·_ : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  unitl  : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr  : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc  : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  ∼·     : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼refl  : {A : Arr n} {f : Tm Γ A} → f ∼ f
  ∼sym   : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h

WkTmTy : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → Tm (WkCon Γ) (WkTy A , WkTy B)
WkTmTy (var x) = var (Wk∈ x)
WkTmTy id = id
WkTmTy (f · g) = WkTmTy f · WkTmTy g

WkTmTm : {n : ℕ} {Γ : Con n} {A : Arr n} {B : Arr n} → Tm Γ A → Tm (Γ ▹ B) A
WkTmTm (var x) = var (drop x)
WkTmTm id = id
WkTmTm (f · g) = WkTmTm f · WkTmTm g

PSTm : {n : ℕ} {Γ : Con n} {A : Arr n} → PS Γ A → Tm Γ A
PSTm start = id
PSTm (ext ps) = {!!} --  WkTmTm (WkTmTy (PSTm ps)) · var here

hid : {n : ℕ} {Γ : Con n} {A B : Ty n} → A ≡ B → Tm Γ (A , B)
hid refl = id

≡→∼ : {n : ℕ} {Γ : Con n} {A : Arr n} {t u : Tm Γ A} → t ≡ u → t ∼ u
≡→∼ refl = ∼refl

-- -- Ty-in-empty-PS : (A : Ty 1) → A ≡ X (# 0)
-- -- Ty-in-empty-PS (X zero) = refl

Ty-in-empty-PS : {A B : Ty 1} → A ≡ B
Ty-in-empty-PS {X zero} {X zero} = refl

Ty-in-empty-PS-refl : {A : Ty 1} → Ty-in-empty-PS {A} {A} ≡ refl
-- Ty-in-empty-PS-refl = UIP _ _
Ty-in-empty-PS-refl {X zero} = refl

-- Tm-in-empty-PS : {A B : Ty 1} (t : Tm ε (A , B)) → t ∼ hid Ty-in-empty-PS
-- Tm-in-empty-PS id = ≡→∼ (sym (cong hid Ty-in-empty-PS-loop))
-- Tm-in-empty-PS (t · u) = ∼trans {!!} (∼trans {!!} {!≡→∼ (sym (cong hid Ty-in-empty-PS-loop))!})

Tm-in-empty-PS : {A B : Ty 1} (t : Tm ε (A , B)) → t ∼ hid Ty-in-empty-PS
Tm-in-empty-PS {X zero} {X zero} id = ∼refl
Tm-in-empty-PS {X zero} {X zero} (_·_ {B = X zero} t u) = ∼trans (∼· (Tm-in-empty-PS t) (Tm-in-empty-PS u)) (unitl id)

data FW {n : ℕ} : (A : Arr n) → Type where
  fw : {i j : Fin n} → i ≥Fin j → FW (X i , X j)

lem-var : {n : ℕ} {Γ : Con n} {A B : Arr n} (ps : PS Γ A) → B ∈ Γ → FW B
lem-var (ext ps) here = fw z≤n
lem-var (ext ps) (drop k) = {!!}
  where
  bla : {!!}
  bla = lem-var ps {!!}

PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (t u : Tm Γ A) → t ∼ u
PSEq start id id = ∼refl
PSEq start id (u · u') = {!!}
PSEq start (t · t') id = {!!}
PSEq start (t · t') (u · u') = {!!}
PSEq (ext ps) t u = {!!}

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

_[_]∼ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ∼ u → σ ∼Sub σ' → t [ σ ] ∼ u [ σ' ]
unitl f [ q ]∼ = ∼trans (unitl (f [ _ ])) (∼refl {f = f} [ q ]∼)
unitr f [ q ]∼ = ∼trans (unitr (f [ _ ])) (∼refl {f = f} [ q ]∼)
assoc f g h [ q ]∼ = ∼trans (assoc (f [ _ ]) (g [ _ ]) (h [ _ ])) (∼· (∼refl {f = f} [ q ]∼) (∼· (∼refl {f = g} [ q ]∼) (∼refl {f = h} [ q ]∼)))
∼· p p' [ q ]∼ = ∼· (p [ q ]∼) (p' [ q ]∼)
∼refl {f = f} [ q ]∼ = lem f q
  where
  lem : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ∼Sub σ' → t [ σ ] ∼ t [ σ' ]
  lem (var here) (σ , p) = p
  lem (var (drop x)) (σ , p) = lem (var x) σ
  lem id p = ∼refl
  lem (f · g) p = ∼· (∼refl {f = f} [ p ]∼) (∼refl {f = g} [ p ]∼)
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
