-- Equivalence between combinatory logic and categorical combinators

open import Prelude
open import Ty
import CL
import CC

F : {n : ℕ} {Γ : Con n} {A : Ty n} → CL.Tm Γ A → CC.Tm Γ A
F = {!!}

G : {n : ℕ} {Γ : Con n} {A : Ty n} → CC.Tm Γ A → CL.Tm Γ A
G = {!!}

F∼ : {n : ℕ} {Γ : Con n} {A : Ty n} (t u : CL.Tm Γ A) → t CL.∼ u → F t CC.∼ F u
F∼ = {!!}

G∼ : {n : ℕ} {Γ : Con n} {A : Ty n} (t u : CC.Tm Γ A) → t CC.∼ u → G t CL.∼ G u
G∼ = {!!}

GF : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CL.Tm Γ A) → G (F t) CL.∼ t
GF = {!!}

FG : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CC.Tm Γ A) → F (G t) CC.∼ t
FG = {!!}
