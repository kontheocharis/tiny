{-# OPTIONS --type-in-type #-}
module FamiliesCode where

open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec

open import Utils
open import CwFwE

postulate
  Λ : Set
  ƛ : (Λ → Λ) → Λ
  _＠_ : Λ → Λ → Λ
  Λη : ∀ f →  ƛ (f ＠_) ≡ f
  Λβ : ∀ f x → (ƛ f) ＠ x ≡ f x
  {-# REWRITE Λη Λβ #-}

module _ where
  open CwFwE-sorts
  open in-CwFwE-sorts
  open CwFwE-core
  open in-CwFwE-core

  fam-s : CwFwE-sorts
  fam-s .Con = Σ[ Γ₀ ∈ Set ] Σ[ Γₑ ∈ Set ] (Γ₀ → Γₑ → Set)
  fam-s .Sub (Γ₀ , Γₑ , Γ₁) (Δ₀ , Δₑ , Δ₁) =
    Σ[ σ₀ ∈ (Γ₀ → Δ₀) ]
    Σ[ σₑ ∈ (Γₑ → Δₑ) ]
    (∀ γ γₑ → Γ₁ γ γₑ → Δ₁ (σ₀ γ) (σₑ γₑ))  
  fam-s .Ty (Γ₀ , Γ₁) = Σ[ A₀ ∈ (Γ₀ → Set) ] (∀ γ → A₀ γ → Λ → Set)
  fam-s .Tm (Γ₀ , Γₑ , Γ₁) ω (A₀ , A₁)
    = Σ[ a₀ ∈ ((γ : Γ₀) → A₀ γ) ]
      Σ[ aₑ ∈ (Γₑ → Λ) ] 
      (∀ γ ns → (γ' : Γ₁ γ ns) → A₁ γ (a₀ γ) (aₑ ns))  
  fam-s .Tm (Γ₀ , Γₑ , Γ₁) z (A₀ , A₁) = (γ : Γ₀) → A₀ γ
  fam-s .#∈ (Γ₀ , Γₑ , Γ₁) = Γₑ → ⊥

  fam-c : CwFwE-core fam-s
  fam-c .id = (λ z₁ → z₁) , (λ z₁ → z₁) , (λ γ ns z₁ → z₁)
  (fam-c ∘ (σ₀ , σₑ , σ₁)) (τ₀ , τₑ , τ₁) =
    (λ z₁ → σ₀ (τ₀ z₁)) ,
    (λ z₁ → σₑ (τₑ z₁)) ,
    (λ γ ns z₁ → σ₁ (τ₀ γ) (τₑ ns) (τ₁ γ ns z₁))
  fam-c .assoc = refl
  fam-c .∘id = refl
  fam-c .id∘ = refl
  fam-c .∙ = ⊤ , ⊤ , λ z₁ z₂ → ⊤
  fam-c .ε = (λ _ → tt) , (λ z₁ → tt) , (λ γ ns _ → tt)
  fam-c .∃!ε = refl
  (fam-c [ A₀ , A₁ ]T) (σ₀ , σₑ , σ₁) = (λ γ → A₀ (σ₀ γ)) , (λ γ a → A₁ (σ₀ γ) a)
  fam-c ._[_] {i = ω} (t₀ , tₑ , t₁) (σ₀ , σₑ , σ₁)
    = (λ γ → t₀ (σ₀ γ)) ,
       (λ z₁ → tₑ (σₑ z₁)) , (λ γ ns γ' → t₁ (σ₀ γ) (σₑ ns) (σ₁ γ ns γ'))
  fam-c ._[_] {i = z} t₀ (σ₀ , σₑ , σ₁) = λ γ → t₀ (σ₀ γ)
  fam-c .[id]T = refl
  fam-c .[id] {i = z} = refl
  fam-c .[id] {i = ω} = refl
  fam-c .[∘]T = refl
  fam-c .[∘] {i = z} = refl
  fam-c .[∘] {i = ω} = refl
  (fam-c ▷[ (Γ₀ , Γₑ , Γ₁) ] ω) (A₀ , A₁)
    = (Σ[ γ ∈ Γ₀ ] A₀ γ) , (Γₑ × Λ) , λ (γ , a) (γₑ , aₑ) → Σ[ γ' ∈ Γ₁ γ γₑ ] A₁ γ a aₑ
  (fam-c ▷[ (Γ₀ , Γₑ , Γ₁) ] z) (A₀ , A₁)
    = (Σ[ γ ∈ Γ₀ ] A₀ γ) , Γₑ , λ (γ , a) → Γ₁ γ
  fam-c .p {i = ω} = (λ z₁ → z₁ .proj₁) , (λ z₁ → z₁ .proj₁) , (λ γ ns z₁ → z₁ .proj₁)
  fam-c .p {i = z} = (λ z₁ → z₁ .proj₁) , (λ z₁ → z₁) , (λ γ ns z₁ → z₁)
  fam-c .q {i = ω} = (λ γ → γ .proj₂) , (λ z₁ → z₁ .proj₂) , (λ γ ns γ' → γ' .proj₂)
  fam-c .q {i = z} = λ γ → γ .proj₂
  fam-c ._,,_ {i = ω} (σ₀ , σ₁) (t₀ , t₁)
    = (λ z₁ → σ₀ z₁ , t₀ z₁)
    , (λ z₁ → σ₁ .proj₁ z₁ , t₁ .proj₁ z₁)
    , λ γ ns z₁ → σ₁ .proj₂ γ ns z₁ , t₁ .proj₂ γ ns z₁
  fam-c ._,,_ {i = z} (σ₀ , σ₁) t₀
    = (λ γa → σ₀ γa , t₀ γa) , σ₁
  fam-c .,∘ {i = z} = refl
  fam-c .,∘ {i = ω} = refl
  fam-c .p,q {i = z} = refl
  fam-c .p,q {i = ω} = refl
  fam-c .p∘, {i = z} = refl
  fam-c .p∘, {i = ω} = refl
  fam-c .q[,] {i = z} = refl
  fam-c .q[,] {i = ω} = refl

  (fam-c [ t ]#) σ γ = t (σ .proj₂ .proj₁ γ)
  fam-c .[id]# = refl
  fam-c .[∘]# = refl
  (fam-c ▷#) (Γ₀ , Γₑ , Γ₁) = Γ₀ , ⊥ , λ x y → ⊥
  fam-c .p# = (λ z₁ → z₁) , (λ ()) , λ γ ()
  fam-c .q# γ = γ
  (fam-c ,# σ) π = σ .proj₁ , π , λ γ γₑ γ' → π γₑ
  fam-c .,#∘ = refl
  fam-c .p,#q = refl
  fam-c .p∘,# {π = π} =
    Σ≡ refl (Σ≡ (funext (λ γ → ⊥-elim-prop (π γ)))
      (funext (λ γ → funext (λ x → ⊥-elim-prop (π x)))))
  fam-c .q[,#] = refl
  fam-c .↓ x γ = x .proj₁ γ
  fam-c .↑ x = x , (λ ()) , λ γ ()
  fam-c .↑↓ {t = t} = Σ≡ refl (Σ≡ (funext (λ ()))
    (funext (λ x → funext (λ y → ⊥-elim-prop y))))
  fam-c .↓↑ = refl

  open Π-structure

  fam-Π : Π-structure fam-s fam-c
  fam-Π .Π ω (A₀ , A₁) (B₀ , B₁) =
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    , λ γ f fₑ → ∀ a aₑ → (a' : A₁ γ a aₑ) → B₁ (γ , a) (f a) (fₑ ＠ aₑ) 
  fam-Π .Π z (A₀ , A₁) (B₀ , B₁) =
    (λ γ → (a : A₀ γ) → B₀ (γ , a))
    , λ γ f fₑ → ∀ a → B₁ (γ , a) (f a) fₑ 
  fam-Π .Π[] {i = ω} = refl
  fam-Π .Π[] {i = z} = refl
  fam-Π .lam {i = z} (f₀ , fₑ , f₁) =
    (λ γ a → f₀ (γ , a))
    , fₑ
    , (λ γ ns γ' a → f₁ (γ , a) ns γ')
  fam-Π .lam {i = ω} (f₀ , fₑ , f₁) =
    (λ γ a → f₀ (γ , a))
    , (λ γₑ → ƛ (λ x → fₑ (γₑ , x)))
    , λ γ ns γ' a aₑ a' → f₁ (γ , a) (ns , aₑ) (γ' , a') 
  -- fam-Π .lam[] = ?
  fam-Π .ap {i = z} (t₀ , tₑ , t₁) =
    (λ (γ , a) → t₀ γ a)
    , tₑ
    , λ (γ , a) ns γ' → t₁ γ ns γ' a
  fam-Π .ap {i = ω} (t₀ , tₑ , t₁) =
    (λ (γ , a) → t₀ γ a)
    , (λ (γₑ , aₑ) → tₑ γₑ ＠ aₑ)
    , λ (γ , a) (γₑ , aₑ) (γ' , a')
      → t₁ γ γₑ γ' a aₑ a'
  fam-Π .Πβ {i = z} = refl
  fam-Π .Πβ {i = ω} = refl
  fam-Π .Πη {i = z} = refl
  fam-Π .Πη {i = ω} = refl

  open U-structure

  fam-U : U-structure fam-s fam-c
  fam-U .U = (λ γ → Σ[ A ∈ Set ] (A → Λ → Set)) , λ γ a x → ⊤
  fam-U .U[] = refl
  fam-U .El t₀ = (λ γ → t₀ γ .proj₁) , λ γ a x → t₀ γ .proj₂ a x
  fam-U .El[] = refl
  fam-U .code (A₀ , A₁) = λ γ → A₀ γ ,  λ a x → A₁ γ a x
  fam-U .code[] = refl
  fam-U .El-code = refl
  fam-U .code-El = refl

-- -- open CwFwE-sorts fam-s
-- -- open in-CwFwE-sorts fam-s
-- -- open CwFwE-core fam-c
-- -- open in-CwFwE-core fam-c
-- -- -- open Π-structure fam-Π
-- -- open U-structure fam-HSU


