open import Agda.Primitive
open import Data.Nat
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}


postulate
  Con : Set

variable
  Γ Δ : Con
  n : ℕ

postulate
  Sub : Con → Con → Set
  Ty : ℕ → Con → Set
  Tm : ∀ Γ → Ty n Γ → Set

variable
  A B : Ty _ _
  σ τ : Sub _ _

coe : ∀ {X Y : Set} → X ≡ Y → X → Y
coe refl x = x

postulate
  _[_]T : Ty n Δ → Sub Γ Δ → Ty n Γ
  _[_]t : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)

  ϕ⇒_ : Con → Con
  _▷_ : (Γ : Con) → Ty n Γ → Con
  Kϕ : Sub Γ (ϕ⇒ Γ)

postulate
  U : (n : ℕ) → Ty (suc n) Γ
  russell : Ty n Γ ≡ Tm Γ (U n)
  {-# REWRITE russell #-}

  √U : (n : ℕ) → Ty (suc n) Γ
  ϕ : Ty zero Γ
  _⇒_ : Ty n Γ → Ty n Γ → Ty n Γ

  pϕ : Sub (Γ ▷ ϕ) Γ
  extϕ : Sub (ϕ⇒ Γ) (ϕ⇒ (Γ ▷ ϕ)) 

postulate
  U[] : (U n) [ σ ]T ≡ U n
  √U[] : (√U n) [ σ ]T ≡ √U n
  ϕ[] : ϕ [ σ ]T ≡ ϕ
  ⇒[] : (A ⇒ B) [ σ ]T ≡ (A [ σ ]T) ⇒ (B [ σ ]T)

  {-# REWRITE U[] √U[] ϕ[] ⇒[] #-}

postulate
  transpose : Tm Γ (√U n) → Tm (ϕ⇒ Γ) (U n)
  untranspose : Tm (ϕ⇒ Γ) (U n) → Tm Γ (√U n)

  tran-untran : ∀ x → transpose {Γ} {n} (untranspose x) ≡ x
  untran-tran : ∀ x → untranspose {Γ} {n} (transpose x) ≡ x
  
  {-# REWRITE tran-untran untran-tran #-}

univ : (n : ℕ) → Tm Γ (U (suc n))
univ n = (√U n)

el : Tm Γ (univ n) → Ty n Γ
el A = (transpose A [ Kϕ ]T)

inuniv : (n : ℕ) → Tm Γ (univ (suc n))
inuniv n = untranspose (√U n)

inel : Tm (Γ ▷ ϕ) (el (inuniv n)) → Tm Γ (univ n)
inel a = untranspose ((transpose a) [ extϕ ]T)

incd : Tm Γ (univ n) → Tm (Γ ▷ ϕ) (el (inuniv n))
incd x = x [ pϕ ]t

inel-incd : ∀ x → inel {Γ} {n} (incd x) ≡ x
inel-incd x = {! !}
  





