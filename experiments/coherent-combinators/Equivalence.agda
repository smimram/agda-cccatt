-- Equivalence between combinatory logic and categorical combinators
--
-- A CL term of type A is translated to a CC *global element* 𝟙 ⇒ A: CC only
-- builds arrow-typed terms, so there is no CC term of type 𝟙 or of an atomic
-- type to receive `T` or an application. Conversely a CC morphism is translated
-- to a CL term of the same (arrow) type by bracket abstraction, and turned back
-- into a point by applying it to `T`.

open import Prelude
open import Ty
import CL
import CC

open CC using (_·_ ; pair ; fst ; snd ; abs ; app ; id ; term)
open CL using (_$_ ; I ; K ; S ; P₁ ; P₂ ; P ; T)

--- From CL to CC

F : {n : ℕ} {Γ : Con' n} {A : Ty n} → CL.Tm Γ A → CC.Tm {!!} (𝟙 , A)
F = {!!}

--- From CC to CL

G : {n : ℕ} {Γ : Con n} {A B : Ty n} → CC.Tm Γ (A , B) → CL.Tm {!!} (A ⇒ B)
G = {!!}

-- --- The translations preserve the equivalences

-- F∼ : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : CL.Tm Γ A} → t CL.∼ u → F t CC.∼ F u
-- F∼ = {!!}

-- G∼ : {n : ℕ} {Γ : Con n} {A : Ty n} {f g : CC.Tm Γ A} → f CC.∼ g → G f CL.∼ G g
-- G∼ = {!!}

-- --- F and G are mutually inverse

-- GF : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CL.Tm Γ A) → G (F t) CL.∼ t
-- GF = {!!}

-- FG : {n : ℕ} {Γ : Con n} {A : Ty n} (f : CC.Tm Γ (𝟙 ⇒ A)) → F (G f) CC.∼ f
-- FG = {!!}
