{-# OPTIONS --type-in-type #-}
module CwFwE where

open import Agda.Primitive
open import Utils
open import Relation.Binary.PropositionalEquality hiding ([_])

data Mode : Set where
  z : Mode
  ω : Mode

opaque
  _*_ : Mode → Mode → Mode
  j * ω = j
  ω * j = j
  z * j = z

private
  variable
    i j : Mode
    
opaque
  unfolding _*_

  j*ω : j * ω ≡ j
  j*ω {z} = refl
  j*ω {ω} = refl

  ω*j : ω * j ≡ j
  ω*j {z} = refl
  ω*j {ω} = refl

  z*j : z * j ≡ z
  z*j {z} = refl
  z*j {ω} = refl

  j*z : j * z ≡ z
  j*z {z} = refl
  j*z {ω} = refl

-- Better definitional computation for _*_
{-# REWRITE j*ω ω*j z*j j*z #-}

record CwF-sorts : Set where
  field
    -- Sorts
    Con : Set
    Sub : Con → Con → Set
    Ty : Con → Set
    #∈ : Con → Set
    Tm : ∀ Γ → Mode → Ty Γ → Set

module in-CwF-sorts (s : CwF-sorts) where
  open CwF-sorts s
  variable
    Γ Δ Θ : Con
    σ τ ρ : Sub _ _
    A B C : Ty _
    t u v : Tm _ _ _
    π : #∈ _

  record CwF-core : Set where
    field
      id : Sub Γ Γ
      _∘_ : (σ : Sub Δ Θ) → (τ : Sub Γ Δ) → Sub Γ Θ
      assoc : ρ ∘ (σ ∘ τ) ≡ (ρ ∘ σ) ∘ τ
      ∘id : id ∘ σ ≡ σ
      id∘ : σ ∘ id ≡ σ

      ∙ : Con
      ε : Sub Γ ∙
      ∃!ε : ε {Γ} ≡ σ
    
      _[_]T : (A : Ty Δ) → (σ : Sub Γ Δ) → Ty Γ
      _[_] : (t : Tm Δ i A) → (σ : Sub Γ Δ) → Tm Γ i (A [ σ ]T)
      _[_]# : (t : #∈ Δ) → (σ : Sub Γ Δ) → #∈ Γ
      [id]T : A [ id ]T ≡ A
      [id] : t [ id ] ≡[ cong (Tm Γ i) [id]T ] t
      [id]# : π [ id ]# ≡ π
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ cong (Tm Γ i) [∘]T ] (t [ σ ]) [ τ ]
      [∘]# : π [ σ ∘ τ ]# ≡ (π [ σ ]#) [ τ ]#
  
    coeTm : A ≡ B → Tm Γ i A → Tm Γ i B
    coeTm p t = subst (Tm _ _) p t
      
    field
      -- Context extension for terms
      _▷[_]_ : (Γ : Con) → Mode → (A : Ty Γ) → Con
      p : Sub (Γ ▷[ i ] A) Γ
      q : Tm (Γ ▷[ i ] A) i (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ i (A [ σ ]T)) → Sub Γ (Δ ▷[ i ] A)
      ,∘ : (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coeTm (sym [∘]T) (t [ ρ ])
      p,q : p {Γ} {i} {A} ,, q ≡ id
      p∘, : p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ cong (Tm Γ i) (trans (sym [∘]T) (cong (A [_]T) p∘,)) ] t

      -- Context extension for #
      _▷# : (Γ : Con) → Con
      p# : Sub (Γ ▷#) Γ
      q# : #∈ (Γ ▷#)
      _,#_ : (σ : Sub Γ Δ) → (π : #∈ Γ) → Sub Γ (Δ ▷#)
      ,#∘ : (σ ,# π) ∘ ρ ≡ (σ ∘ ρ) ,# (π [ ρ ]#)
      p,#q : p# {Γ} ,# q# ≡ id
      p∘,# : p# ∘ (σ ,# π) ≡ σ
      q[,#] : q# [ σ ,# π ]# ≡ π
      
      -- Conversion between terms
      ↓ : Tm (Γ ▷#) ω (A [ p# ]T) → Tm Γ z A
      ↑ : Tm Γ z A → Tm (Γ ▷#) ω (A [ p# ]T)
      ↑↓ : ↑ (↓ t) ≡ t
      ↓↑ : ↓ (↑ t) ≡ t

    ⟨_⟩ : (t : Tm Γ i A) → Sub Γ (Γ ▷[ i ] A)
    ⟨ t ⟩ = id ,, (t [ id ])

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷[ i ] (A [ σ ]T)) (Δ ▷[ i ] A)
    σ ⁺ = (σ ∘ p) ,, subst (Tm _ _) (sym [∘]T) q
  

  module in-CwF-core (c : CwF-core) where
    open CwF-core c

  --   record Π-structure  : Set where
  --     field
  --       Π : (i : Mode) → (A : Ty Γ) → (B : Ty (Γ ▷[ z ] A)) → Ty Γ
  --       Π[] : (Π i A B) [ σ ]T ≡ Π i (A [ σ ]T) (B [ σ ⁺ ]T)

  --       lam : (f : Tm (Γ ▷[ i ] A) ω B) → Tm Γ ω (Π i A (B [ ? ]T))
  --       lam[] : (lam t) [ σ ] ≡[ cong (Tm _) Π[] ] lam (t [ σ ⁺ ])

  --       ap : (f : Tm Γ (Π A B)) → Tm (Γ ▷[ i ] A) B

  --       Πβ : ap (lam t) ≡ t
  --       Πη : lam (ap t) ≡ t

  --     _⇒_ : Ty Γ → Ty Γ → Ty Γ
  --     A ⇒ B = Π A (B [ p ]T)

    record U-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ z U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (subst (Tm _ _) U[] (t [ σ ]))

        code : (A : Ty Γ) → Tm Γ z U
        code[] : (code A) [ σ ] ≡[ cong (Tm _ _) U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t

  --     _[_]U : (t : Tm Δ U) → (σ : Sub Γ Δ) → Tm Γ U
  --     _[_]U t σ = coeTm U[] (t [ σ ])

  --     _⁺U : (σ : Sub Γ Δ) → Sub (Γ ▷[ i ] El (t [ σ ]U)) (Δ ▷[ i ] El t)
  --     σ ⁺U = ((σ ∘ p) ,, subst (Tm _) (trans (cong (_[ p ]T) (sym El[])) (sym [∘]T)) q)

  --     TmU : ∀ Γ → Tm Γ U → Set
  --     TmU Γ t = Tm Γ (El t)

  --     _[_]u : (a : TmU Δ t) → (σ : Sub Γ Δ) → TmU Γ (t [ σ ]U)
  --     _[_]u a σ = coeTm El[] (a [ σ ])

  --     _▷[_]U_ : (Γ : Con) → Mode → Tm Γ U → Con
  --     Γ ▷[ i ]U t = Γ ▷[ i ] El t

  --   record ΠU-structure (univ : U-structure) : Set where
  --     open U-structure univ
  --     field
  --       ΠU : (t : Tm Γ U) → (u : Tm (Γ ▷[ i ]U t) U) → Tm Γ U
  --       ΠU[] : (ΠU t u) [ σ ]U ≡ ΠU (t [ σ ]U) (u [ σ ⁺U ]U)

  --       lamU : (f : TmU (Γ ▷[ i ]U t) u) → TmU Γ (ΠU t u)
  --       lamU[] : (lamU t) [ σ ]u ≡[ cong (TmU _) ΠU[] ] lamU (t [ σ ⁺U ]u)

  --       apU : (f : TmU Γ (ΠU t u)) → TmU (Γ ▷[ i ]U t) u

  --       ΠβU : apU (lamU t) ≡ t
  --       ΠηU : lamU (apU t) ≡ t



