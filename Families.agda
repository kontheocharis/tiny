{-# OPTIONS --type-in-type #-}
module Families where

open import CwF
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open CwF-sorts
open CwF-core

fam-s : CwF-sorts
fam-s .Con = Σ[ Γ₀ ∈ Set ] (Γ₀ → Set)
fam-s .Sub (Γ₀ , Γ₁) (Δ₀ , Δ₁) = Σ[ σ₀ ∈ (Γ₀ → Δ₀) ] (∀ γ → Γ₁ γ → Δ₁ (σ₀ γ))  
fam-s .Ty (Γ₀ , Γ₁) =  Σ[ A₀ ∈ (Γ₀ → Set) ] (∀ γ → Γ₁ γ → A₀ γ → Set)
fam-s .Tm (Γ₀ , Γ₁) (A₀ , A₁) = Σ[ a₀ ∈ ((γ : Γ₀) → A₀ γ) ] (∀ γ → (γ' : Γ₁ γ) → A₁ γ γ' (a₀ γ))  

fam-c : CwF-core fam-s
fam-c .id = (λ γ → γ) , (λ γ γ' → γ') 
(fam-c ∘ (σ₀ , σ₁)) (τ₀ , τ₁) = (λ γ → σ₀ (τ₀ γ)) , (λ γ γ' → σ₁ (τ₀ γ) (τ₁ γ γ'))
fam-c .assoc = refl
fam-c .∘id = refl
fam-c .id∘ = refl
fam-c .∙ = ⊤ , λ z → ⊤
fam-c .ε = (λ _ → tt) , (λ γ _ → tt)
fam-c .∃!ε = refl
(fam-c [ A₀ , A₁ ]T) (σ₀ , σ₁) = (λ γ → A₀ (σ₀ γ)) , (λ γ γ' a → A₁ (σ₀ γ) (σ₁ γ γ') a)
fam-c ._[_] (t₀ , t₁) (σ₀ , σ₁) = (λ γ → t₀ (σ₀ γ)) , (λ γ γ' → t₁ (σ₀ γ) (σ₁ γ γ'))
fam-c .[id]T = refl
fam-c .[id] = refl
fam-c .[∘]T = refl
fam-c .[∘] = refl
(fam-c ▷ (Γ₀ , Γ₁)) (A₀ , A₁) = (Σ[ γ ∈ Γ₀ ] A₀ γ) , λ (γ , a) → Σ[ γ' ∈ Γ₁ γ ] A₁ γ γ' a
fam-c .p = (λ (γ , a) → γ) , (λ γa (γ' , a') → γ')
fam-c .q = (λ (γ , a) → a) , (λ γa (γ' , a') → a')
(fam-c ,, (σ₀ , σ₁)) (t₀ , t₁) = (λ γa → σ₀ γa , t₀ γa) , (λ γa γ'a' → σ₁ γa γ'a' , t₁ γa γ'a')
fam-c .,∘ = refl
fam-c .p,q = refl
fam-c .p∘, = refl
fam-c .q[,] = refl


fam-Π : Π-structure fam-s fam-c
fam-Π = ?

-- fam-c .Π = {!!}
-- fam-c .Π[] = {!!}
-- fam-c .lam = {!!}
-- fam-c .lam[] = {!!}
-- fam-c .ap = {!!}
-- fam-c .β = {!!}
-- fam-c .η = {!!}
-- fam-c .U = {!!}
-- fam-c .U[] = {!!}
-- fam-c .El = {!!}
-- fam-c .El[] = {!!}
-- fam-c .code = {!!}
-- fam-c .code[] = {!!}
-- fam-c .El-code = {!!}
-- fam-c .code-El = {!!}
