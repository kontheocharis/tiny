module Utils where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (Level; _⊔_; suc)
open import Data.Product
open import Data.Empty
open import Agda.Builtin.Sigma

private variable
  ℓ ℓ' : Level
  A B : Set ℓ
  x y z : A

infix 4 _≡_
data _≡_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  instance refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

postulate
  coe : A ≡ B → A → B
  coe-eq : {p : A ≡ A} → coe p x ≡ x
  {-# REWRITE coe-eq #-}

  funext : ∀ {B : A → Set ℓ} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl p = p

subst : (P : A → Set ℓ) (p : x ≡ y) → P x → P y
subst P p a = coe (cong P p) a

_∣_≡[_]_ : ∀ {A : Set ℓ} (F : A → Set ℓ') {a} (f : F a) {b} (p : a ≡ b) (g : F b) → Prop ℓ'
_∣_≡[_]_ F f p g = subst F p f ≡ g

infix 4 _≡[_]_

_≡[_]_ : ∀ {A B : Set ℓ} (a : A) (p : A ≡ B) (b : B) → Prop ℓ
_≡[_]_ {A} {B} a p b = coe p a ≡ b

record _≃_ (A : Set ℓ) (B : Set ℓ) : Set ℓ where
  field
    to : A → B
    from : B → A
    to-from : ∀ x → to (from x) ≡ x
    from-to : ∀ x → from (to x) ≡ x

open _≃_ public

record _true (A : Prop ℓ) : Set ℓ where
  constructor by
  field
    witness : A

open _true public

record ΣProp {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,P_
  field
    fst : A
    snd : B fst

open ΣProp public

⊥-elim-prop : ∀ {w} {Whatever : Prop w} → ⊥ → Whatever
⊥-elim-prop ()

module _ {A : Set ℓ} {B : A → Set ℓ'} where
  Σ≡ : {p₁ p₂ : Σ A B} (p : p₁ .proj₁ ≡ p₂ .proj₁) → subst B p (p₁ .proj₂) ≡ (p₂ .proj₂) → p₁ ≡ p₂
  Σ≡ refl refl = refl

  ≡Σ : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂)
    → ΣProp (p₁ .proj₁ ≡ p₂ .proj₁) (λ p → subst B p (p₁ .proj₂) ≡ (p₂ .proj₂))
  ≡Σ refl = refl ,P refl
