module Utils where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; cong₂; subst)
open import Level using (Level; _⊔_; suc)

variable
  ℓ ℓ' : Level

postulate
  funext : Extensionality ℓ ℓ'

{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡[_]_
infix 4 _∣_≡[_]_

coe : ∀ {A B : Set ℓ} (p : A ≡ B) → A → B
coe p = subst (λ s → s) p

_∣_≡[_]_ : ∀ {A : Set ℓ} (F : A → Set ℓ') {a} (f : F a) {b} (p : a ≡ b) (g : F b) → Set ℓ'
_∣_≡[_]_ F f p g = subst F p f ≡ g

_≡[_]_ : ∀ {A B : Set ℓ} (a : A) (p : A ≡ B) (b : B) → Set ℓ
_≡[_]_ {A} {B} a p b = coe p a ≡ b
