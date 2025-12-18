{-# OPTIONS --type-in-type --lossy-unification #-}
module FamiliesAlt where

open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Utils
open import CwF

-- Alternative families model, where types do not depend on fiber data
--
-- This is an explicit construction of the situation where we use the right
-- adjoint to the tiny object to interpret universes

module _ where
  open CwF-sorts
  open in-CwF-sorts
  open CwF-core
  open in-CwF-core

  fam-s : CwF-sorts
  fam-s .Con = Σ[ Γ₀ ∈ Set ] (Γ₀ → Set)
  fam-s .Sub (Γ₀ , Γ₁) (Δ₀ , Δ₁) = Σ[ σ₀ ∈ (Γ₀ → Δ₀) ] (∀ γ → Γ₁ γ → Δ₁ (σ₀ γ))  
  fam-s .Ty (Γ₀ , Γ₁) =  Σ[ A₀ ∈ (Γ₀ → Set) ] (∀ γ → A₀ γ → Set)
  fam-s .Tm (Γ₀ , Γ₁) (A₀ , A₁) = Σ[ a₀ ∈ ((γ : Γ₀) → A₀ γ) ] (∀ γ → (γ' : Γ₁ γ) → A₁ γ (a₀ γ))  

  fam-c : CwF-core fam-s
  fam-c .id = (λ γ → γ) , (λ γ γ' → γ') 
  (fam-c ∘ (σ₀ , σ₁)) (τ₀ , τ₁) = (λ γ → σ₀ (τ₀ γ)) , (λ γ γ' → σ₁ (τ₀ γ) (τ₁ γ γ'))
  fam-c .assoc = refl
  fam-c .∘id = refl
  fam-c .id∘ = refl
  fam-c .∙ = ⊤ , λ z → ⊤
  fam-c .ε = (λ _ → tt) , (λ γ _ → tt)
  fam-c .∃!ε = refl
  (fam-c [ A₀ , A₁ ]T) (σ₀ , σ₁) = (λ γ → A₀ (σ₀ γ)) , (λ γ a → A₁ (σ₀ γ) a)
  fam-c ._[_] (t₀ , t₁) (σ₀ , σ₁) = (λ γ → t₀ (σ₀ γ)) , (λ γ γ' → t₁ (σ₀ γ) (σ₁ γ γ'))
  fam-c .[id]T = refl
  fam-c .[id] = refl
  fam-c .[∘]T = refl
  fam-c .[∘] = refl
  (fam-c ▷ (Γ₀ , Γ₁)) (A₀ , A₁) = (Σ[ γ ∈ Γ₀ ] A₀ γ) , λ (γ , a) → Σ[ γ' ∈ Γ₁ γ ] A₁ γ a
  fam-c .p = (λ (γ , a) → γ) , (λ γa (γ' , a') → γ')
  fam-c .q = (λ (γ , a) → a) , (λ γa (γ' , a') → a')
  (fam-c ,, (σ₀ , σ₁)) (t₀ , t₁) = (λ γa → σ₀ γa , t₀ γa) , (λ γa γ'a' → σ₁ γa γ'a' , t₁ γa γ'a')
  fam-c .,∘ = refl
  fam-c .p,q = refl
  fam-c .p∘, = refl
  fam-c .q[,] = refl

  open Π-structure

  fam-Π : Π-structure fam-s fam-c
  fam-Π .Π (A₀ , A₁) (B₀ , B₁) =
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    , λ γ f → ∀ a → (a' : A₁ γ a) → B₁ (γ , a) (f a)
  fam-Π .Π[] = refl
  fam-Π .lam (f₀ , f₁) = (λ γ a → f₀ (γ , a)) , (λ γ γ' a a' → f₁ (γ , a) (γ' , a'))
  fam-Π .lam[] = refl
  fam-Π .ap (t₀ , t₁) = (λ (γ , a) → t₀ γ a) , (λ (γ , a) (γ' , a') → t₁ γ γ' a a')
  fam-Π .Πβ = refl
  fam-Π .Πη = refl

  open U-small-structure
  open U-big-structure

  -- Alternative universe construction
  fam-HSU : U-small-structure fam-s fam-c
  fam-HSU .U = (λ γ → Σ[ A ∈ Set ] (A → Set)) , λ γ a → ⊤
  fam-HSU .U[] = refl
  fam-HSU .El (t₀ , _) = (λ γ → t₀ γ .proj₁) , λ γ a → t₀ γ .proj₂ a
  fam-HSU .El[] = refl

  fam-HSU-b : U-big-structure fam-s fam-c fam-HSU
  fam-HSU-b .code (A₀ , A₁) = (λ γ → A₀ γ , A₁ γ) , λ γ γ' → tt
  fam-HSU-b .code[] = refl
  fam-HSU-b .El-code = refl
  fam-HSU-b .code-El = refl

open CwF-sorts fam-s
open in-CwF-sorts fam-s
open CwF-core fam-c
open in-CwF-core fam-c
open Π-structure fam-Π
open U-small-structure fam-HSU

-- Phase separator (yoneda of base)
ϕ : Ty Γ
ϕ = (λ γ → ⊤) , λ γ a → ⊥

-- ϕ is a proposition
ϕ-prop : (t u : Tm Γ (ϕ {Γ})) → t ≡ u
ϕ-prop t u = refl

-- Exponentiating by ϕ isolates the base
exp-ϕ : {A : Ty Γ} → Tm Γ (_⇒_ {Γ} (ϕ {Γ}) A) ≃ (∀ γ → A .proj₁ γ)
exp-ϕ .to (t₀ , t₁) = λ γ → t₀ γ tt
exp-ϕ .from t = (λ γ a → t γ) , λ γ γ' a ()
exp-ϕ .to-from = λ x → refl
exp-ϕ .from-to (t₀ , t₁) = Σ≡ refl (funext λ x → funext λ y → funext  λ z → funext λ ()) 

open Π-structure
