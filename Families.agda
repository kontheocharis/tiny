{-# OPTIONS --type-in-type #-}
module Families where

open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Utils
open import CwF

module _ where
  open CwF-sorts
  open in-CwF-sorts
  open CwF-core
  open in-CwF-core

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

  open Π-structure

  fam-Π : Π-structure fam-s fam-c
  fam-Π .Π (A₀ , A₁) (B₀ , B₁) =
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    , λ γ γ' f → ∀ a → (a' : A₁ γ γ' a) → B₁ (γ , a) (γ' , a') (f a)
  fam-Π .Π[] = refl
  fam-Π .lam (f₀ , f₁) = (λ γ a → f₀ (γ , a)) , (λ γ γ' a a' → f₁ (γ , a) (γ' , a'))
  fam-Π .lam[] = refl
  fam-Π .ap (t₀ , t₁) = (λ (γ , a) → t₀ γ a) , (λ (γ , a) (γ' , a') → t₁ γ γ' a a')
  fam-Π .Πβ = refl
  fam-Π .Πη = refl

  open U-small-structure
  open U-big-structure
  open ΠU-structure

  -- Hofmann-Streicher universe
  fam-HSU : U-small-structure fam-s fam-c
  fam-HSU .U = (λ γ → Set) , λ γ γ' A → A → Set
  fam-HSU .U[] = refl
  fam-HSU .El (t₀ , t₁) = t₀ , t₁
  fam-HSU .El[] = refl

  fam-HSU-b : U-big-structure fam-s fam-c fam-HSU
  fam-HSU-b .code (A₀ , A₁) = A₀ , A₁ 
  fam-HSU-b .code[] = refl
  fam-HSU-b .El-code = refl
  fam-HSU-b .code-El = refl

  -- Squashed universe
  fam-SQ : U-small-structure fam-s fam-c
  fam-SQ .U = (λ γ → Σ[ A ∈ Set ] (A → Set)) , λ γ γ' A → ⊤
  fam-SQ .U[] = refl
  fam-SQ .El (t₀ , _) = (λ γ → t₀ γ .proj₁) , (λ γ γ' a → t₀ γ .proj₂ a)
  fam-SQ .El[] = refl

  -- Pi types in the squashed universe
  fam-SQΠ : ΠU-structure fam-s fam-c fam-SQ
  fam-SQΠ .ΠU (A , _) (B , _)
    = (λ γ → ((a : A γ .proj₁) → B (γ , a) .proj₁)
      , λ f → ∀ a → (a' : A γ .proj₂ a) → B (γ , a) .proj₂ (f a))
      , λ γ γ' → tt
  fam-SQΠ .ΠU[] = refl
  fam-SQΠ .lamU = λ f →
                     (λ γ a → f .proj₁ (γ , a)) ,
                     (λ γ γ' a a' → f .proj₂ (γ , a) (γ' , a'))
  fam-SQΠ .lamU[] = refl
  fam-SQΠ .apU = λ f →
                    (λ γ → f .proj₁ (γ .proj₁) (γ .proj₂)) ,
                    (λ γ γ' → f .proj₂ (γ .proj₁) (γ' .proj₁) (γ .proj₂) (γ' .proj₂))
  fam-SQΠ .ΠβU = refl
  fam-SQΠ .ΠηU = refl

open CwF-sorts fam-s
open in-CwF-sorts fam-s
open CwF-core fam-c
open in-CwF-core fam-c
open Π-structure fam-Π
open U-small-structure fam-HSU
open U-big-structure fam-HSU-b

module S = U-small-structure fam-SQ
module SΠ = ΠU-structure fam-SQΠ 

-- The constructions below are all obviously natural in Γ

-- Phase separator (yoneda of base)
ϕ : Ty Γ
ϕ = (λ γ → ⊤) , λ γ γ' a → ⊥

-- ϕ is a proposition
ϕ-prop : (t u : Tm Γ ϕ) → t ≡ u
ϕ-prop t u = refl

-- Squashed types are unaffected by ϕ
Φ⇒SU : Tm Γ (ϕ ⇒ S.U) ≃ Tm Γ S.U
Φ⇒SU .to (A , _) = (λ γ → A γ tt) , (λ γ γ' → tt)
Φ⇒SU .from (A , _) = (λ γ a → A γ) , (λ γ γ' a a' → tt)
Φ⇒SU .to-from (A , _) = refl
Φ⇒SU .from-to (A , _) = refl

-- All closed types can be moved either way
closed-iso : Ty ∙ ≃ Tm ∙ S.U
closed-iso .to (A₀ , A₁) = (λ _ → A₀ tt , (λ a → A₁ tt tt a)) , (λ γ γ' → tt)
closed-iso .from (A , _) = ( λ _ → A tt .proj₁) , (λ _ _ a → A tt .proj₂ a)
closed-iso .to-from x = refl
closed-iso .from-to x = refl

-- ϕ-modal types are a subuniverse of squashed types
base-in : Tm Γ (ϕ ⇒ U) → Tm Γ S.U
base-in (t₀ , t₁) = (λ γ → t₀ γ tt , λ _ → ⊤) , (λ γ γ' → tt)

base-in-inj : (t u : Tm Γ (ϕ ⇒ U)) → base-in t ≡ base-in u → t ≡ u
base-in-inj (t₀ , t₁) (u₀₁ , u₁) p =
  let (p₀ ,P p₁) = ≡Σ p in
  let p₀' = (λ γ → ≡Σ (cong (λ x → x γ) p₀)) in
  Σ≡ (funext (λ γ → funext (λ tt → p₀' γ .fst)))
  (funext (λ γ → funext (λ γ' → funext (λ tt → funext (λ ())))) )

-- Squashed types are included in types
squash-in : Tm Γ S.U → Ty Γ
squash-in (t , _) = (λ γ → t γ .proj₁) , (λ γ γ' a → t γ .proj₂ a)

-- but this only injective for closed codes!
squash-in-inj : (t u : Tm ∙ S.U) → squash-in t ≡ squash-in u → t ≡ u
squash-in-inj (t₀ , t₁) (u₀₁ , u₁) p =
  let (p₀ ,P p₁) = ≡Σ p in
  let p₀' = cong (λ x → x tt) p₀ in
  let p₁' = cong (λ x → x tt tt) p₁ in
  Σ≡ (funext (λ tt → Σ≡ p₀' p₁')) refl

