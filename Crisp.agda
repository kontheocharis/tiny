{-# OPTIONS --cohesion #-}

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Polymorphic

{-# BUILTIN REWRITE _≡_ #-}

variable
  ℓ : Level
  @♭ ♭ℓ : Level
  @♭ A B : Set ♭ℓ

data ♭ (@♭ X : Set ♭ℓ) : Set ♭ℓ where
  flat : (@♭ x : X) → ♭ X

unflat : ♭ A → A
unflat (flat x) = x

postulate
  ϕ : Prop
  √ : (@♭ x : Set ℓ) → Set ℓ

module _ {@♭ ♭ℓ : Level} {@♭ A B : Set ♭ℓ} where
  postulate
    @♭ R : (@♭ _ : (ϕ → A) → B) → A → √ B
    @♭ Rinv : (@♭ _ : A → √ B) → (ϕ → A) → B
    RRinv : (@♭ x : A → (√ B)) (@♭ y : A) → R (Rinv x) y ≡ x y
    RinvR : (@♭ x : (ϕ → A) → B) (@♭ y : (ϕ → A)) → Rinv (R x) y ≡ x y

    {-# REWRITE RRinv RinvR #-}

module _ {@♭ ♭ℓ : Level} {@♭ A : Set ♭ℓ} where
  @♭ unit : (@♭ _ : A) → √ (ϕ → A)
  unit a = R {A = A} {B = ϕ → A} (λ m → m) a

  @♭ counit : (@♭ _ : (ϕ → √ A)) → A
  counit a = Rinv {A = √ A} {B = A} ((λ m → m)) a

  @♭ op : (@♭ _ : √ A) → A
  op x = counit (λ _ → x)

  @♭ cl : (@♭ _ : A) → √ A
  cl x = R {A = ⊤} (λ _ → x) tt

U : (@♭ ℓ : Level) → Set (lsuc ℓ)
U ℓ = ♭ (√ (Set ℓ))

El : U ♭ℓ → Set ♭ℓ
El (flat x) = counit (λ _ → x)

u : (@♭ ℓ : Level) → U (lsuc ℓ)
u ℓ = flat (R (λ x → U ℓ) (flat tt))

el : El {lsuc ♭ℓ} (u ♭ℓ) → U ♭ℓ
el a = flat (R (Rinv  λ _ → {! !}) ( flat tt))

cd : U ♭ℓ → El {lsuc ♭ℓ} (u ♭ℓ)
cd A = {! !}

