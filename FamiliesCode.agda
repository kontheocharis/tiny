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

ConΛ : Set
ConΛ = ℕ

SubΛ : ConΛ → ConΛ → Set
SubΛ Γ Δ = Vec Λ Γ → Vec Λ Δ

TmΛ : ConΛ → Set
TmΛ Γ = Vec Λ Γ → Λ

is-empty : ∀ {A} {v : Vec A 0} → [] ≡ v
is-empty {v = []} = refl

head-tail : ∀ {A n} {v : Vec A (suc n)} → head v ∷ tail v ≡ v
head-tail {v = x ∷ xs} = refl

subst-coh : ∀ {A} {P : A → Set} {x} {p : x ≡ x} {y} → subst P p y ≡ y
subst-coh {p = refl} = refl

module _ where
  open CwFwE-sorts
  open in-CwFwE-sorts
  open CwFwE-core
  open in-CwFwE-core

  fam-s : CwFwE-sorts
  fam-s .Con = Σ[ Γ₀ ∈ Set ] Σ[ n ∈ ConΛ ] (Γ₀ → Vec Λ n → Set)
  fam-s .Sub (Γ₀ , Γₑ , Γ₁) (Δ₀ , Δₑ , Δ₁) =
    Σ[ σ₀ ∈ (Γ₀ → Δ₀) ]
    Σ[ σₑ ∈ SubΛ Γₑ Δₑ ]
    (∀ γ → ∀ ns → Γ₁ γ ns → Δ₁ (σ₀ γ) (σₑ ns))  
  fam-s .Ty (Γ₀ , Γ₁) = Σ[ A₀ ∈ (Γ₀ → Set) ] (∀ γ → A₀ γ → Λ → Set)
  fam-s .Tm (Γ₀ , Γₑ , Γ₁) ω (A₀ , A₁)
    = Σ[ a₀ ∈ ((γ : Γ₀) → A₀ γ) ]
      Σ[ aₑ ∈ TmΛ Γₑ ] 
      (∀ γ ns → (γ' : Γ₁ γ ns) → A₁ γ (a₀ γ) (aₑ ns))  
  fam-s .Tm (Γ₀ , Γₑ , Γ₁) z (A₀ , A₁) = (γ : Γ₀) → A₀ γ
  fam-s .#∈ (Γ₀ , Γₑ , Γ₁) = (γ : Γ₀) → ∀ ns → Γ₁ γ ns → ⊥

  fam-c : CwFwE-core fam-s
  fam-c .id = (λ z₁ → z₁) , (λ z₁ → z₁) , (λ γ ns z₁ → z₁)
  (fam-c ∘ (σ₀ , σₑ , σ₁)) (τ₀ , τₑ , τ₁) =
    (λ z₁ → σ₀ (τ₀ z₁)) ,
    (λ z₁ → σₑ (τₑ z₁)) ,
    (λ γ ns z₁ → σ₁ (τ₀ γ) (τₑ ns) (τ₁ γ ns z₁))
  fam-c .assoc = refl
  fam-c .∘id = refl
  fam-c .id∘ = refl
  fam-c .∙ = ⊤ , 0 , λ z₁ z₂ → ⊤
  fam-c .ε = (λ _ → tt) , (λ z₁ → []) , (λ γ ns _ → tt)
  fam-c .∃!ε = Σ≡ refl (Σ≡ (funext (λ _ → is-empty)) refl)
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
    = (Σ[ γ ∈ Γ₀ ] A₀ γ) , suc Γₑ , λ (γ , a) ns → Σ[ γ' ∈ Γ₁ γ (tail ns) ] A₁ γ a (head ns)
  (fam-c ▷[ (Γ₀ , Γₑ , Γ₁) ] z) (A₀ , A₁)
    = (Σ[ γ ∈ Γ₀ ] A₀ γ) , Γₑ , λ (γ , a) → Γ₁ γ
  fam-c .p {i = ω} = (λ z₁ → z₁ .proj₁) , tail , (λ γ ns z₁ → z₁ .proj₁)
  fam-c .p {i = z} = (λ z₁ → z₁ .proj₁) , (λ z₁ → z₁) , (λ γ ns z₁ → z₁)
  fam-c .q {i = ω} = (λ γ → γ .proj₂) , head , (λ γ ns γ' → γ' .proj₂)
  fam-c .q {i = z} = λ γ → γ .proj₂
  fam-c ._,,_ {i = ω} (σ₀ , σ₁) (t₀ , t₁)
    = (λ z₁ → σ₀ z₁ , t₀ z₁)
    , (λ z₁ → t₁ .proj₁ z₁ ∷ σ₁ .proj₁ z₁)
    , λ γ ns z₁ → σ₁ .proj₂ γ ns z₁ , t₁ .proj₂ γ ns z₁
  fam-c ._,,_ {i = z} (σ₀ , σ₁) t₀
    = (λ γa → σ₀ γa , t₀ γa) , σ₁
  fam-c .,∘ {i = z} = refl
  fam-c .,∘ {i = ω} = refl
  fam-c .p,q {i = z} = refl
  fam-c .p,q {i = ω} = Σ≡ refl (Σ≡ (funext (λ x → head-tail)) refl)
  fam-c .p∘, {i = z} = refl
  fam-c .p∘, {i = ω} = refl
  fam-c .q[,] {i = z} = refl
  fam-c .q[,] {i = ω} = refl

--   (fam-c [ t ]#) σ γ x = t (σ .proj₁ γ) (σ .proj₂ γ x) 
--   fam-c .[id]# = refl
--   fam-c .[∘]# = refl
--   (fam-c ▷#) (Γ₀ , Γ₁) = Γ₀ , (λ _ → ⊥)
--   fam-c .p# = (λ z₁ → z₁) , λ γ ()
--   fam-c .q# γ x = x
--   (fam-c ,# σ) π = σ .proj₁ , π
--   fam-c .,#∘ = refl
--   fam-c .p,#q = refl
--   fam-c .p∘,# {π = π} = Σ-≡,≡→≡ (refl , funext (λ γ → funext λ γ' → ⊥-elim (π γ γ'))) 
--   fam-c .q[,#] = refl
--   fam-c .↓ x γ = x .proj₁ γ
--   fam-c .↑ x = x , λ γ ()
--   fam-c .↑↓ {t = t} = Σ-≡,≡→≡ (refl , funext λ x → funext λ ()) 
--   fam-c .↓↑ = refl


--   -- open Π-structure

--   -- fam-Π : Π-structure fam-s fam-c
--   -- fam-Π .Π (A₀ , A₁) (B₀ , B₁) =
--   --   (λ γ → (a : A₀ γ) → B₀ (γ , a))
--   --   , λ γ f → ∀ a → (a' : A₁ γ a) → B₁ (γ , a) (f a)
--   -- fam-Π .Π[] = refl
--   -- fam-Π .lam (f₀ , f₁) = (λ γ a → f₀ (γ , a)) , (λ γ γ' a a' → f₁ (γ , a) (γ' , a'))
--   -- fam-Π .lam[] = refl
--   -- fam-Π .ap (t₀ , t₁) = (λ (γ , a) → t₀ γ a) , (λ (γ , a) (γ' , a') → t₁ γ γ' a a')
--   -- fam-Π .Πβ = refl
--   -- fam-Π .Πη = refl

--   open U-structure

--   fam-U : U-structure fam-s fam-c
--   fam-U .U = (λ γ → Σ[ A ∈ Set ] (A → Set)) , λ γ a → ⊤
--   fam-U .U[] = refl
--   fam-U .El t₀ = (λ γ → t₀ γ .proj₁) , λ γ a → t₀ γ .proj₂ a
--   fam-U .El[] = refl
--   fam-U .code (A₀ , A₁) = λ γ → A₀ γ , A₁ γ
--   fam-U .code[] = refl
--   fam-U .El-code = refl
--   fam-U .code-El = refl

-- -- open CwFwE-sorts fam-s
-- -- open in-CwFwE-sorts fam-s
-- -- open CwFwE-core fam-c
-- -- open in-CwFwE-core fam-c
-- -- -- open Π-structure fam-Π
-- -- open U-structure fam-HSU

-- -- -- Phase separator (yoneda of base)
-- -- ϕ : Ty Γ
-- -- ϕ = (λ γ → ⊤) , λ γ a → ⊥

-- -- -- ϕ is a proposition
-- -- ϕ-prop : (t u : Tm Γ (ϕ {Γ})) → t ≡ u
-- -- ϕ-prop t u = refl

-- -- -- Exponentiating by ϕ isolates the base
-- -- exp-ϕ : {A : Ty Γ} → Tm Γ (_⇒_ {Γ} (ϕ {Γ}) A) ≃ (∀ γ → A .proj₁ γ)
-- -- exp-ϕ .to (t₀ , t₁) = λ γ → t₀ γ tt
-- -- exp-ϕ .from t = (λ γ a → t γ) , λ γ γ' a ()
-- -- exp-ϕ .to-from = λ x → refl
-- -- exp-ϕ .from-to (t₀ , t₁) = Σ-≡,≡→≡ (refl , funext λ x → funext λ y → funext  λ z → funext λ ()) 

-- -- open Π-structure
