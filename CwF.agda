{-# OPTIONS --type-in-type #-}
module CwF where

open import Agda.Primitive
open import Utils
open import Relation.Binary.PropositionalEquality hiding ([_])

record CwF-sorts : Set where
  field
    -- Sorts
    Con : Set
    Sub : Con → Con → Set
    Ty : Con → Set
    Tm : ∀ Γ → Ty Γ → Set

module _ (s : CwF-sorts) where
  open CwF-sorts s
  variable
    Γ Δ Θ : Con
    σ τ ρ : Sub _ _
    A B C : Ty _
    t u v : Tm _ _

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
      _[_] : (t : Tm Δ A) → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
      [id]T : A [ id ]T ≡ A
      [id] : t [ id ] ≡[ cong (Tm Γ) [id]T ] t
      [∘]T : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T
      [∘] : t [ σ ∘ τ ] ≡[ cong (Tm Γ) [∘]T ] (t [ σ ]) [ τ ]
  
    coeTm : A ≡ B → Tm Γ A → Tm Γ B
    coeTm p t = subst (Tm _) p t
      
    field
      -- Context extension
      _▷_ : (Γ : Con) → (A : Ty Γ) → Con
      p : Sub (Γ ▷ A) Γ
      q : Tm (Γ ▷ A) (A [ p ]T)
      _,,_ : (σ : Sub Γ Δ) → (t : Tm Γ (A [ σ ]T)) → Sub Γ (Δ ▷ A)
      ,∘ : (σ ,, t) ∘ ρ ≡ (σ ∘ ρ) ,, coeTm (sym [∘]T) (t [ ρ ])
      p,q : p {Γ} {A} ,, q ≡ id
      p∘, : p ∘ (σ ,, t) ≡ σ
      q[,] : q [ σ ,, t ] ≡[ cong (Tm Γ) (trans (sym [∘]T) (cong (A [_]T) p∘,)) ] t


    ⟨_⟩ : (t : Tm Γ A) → Sub Γ (Γ ▷ A)
    ⟨ t ⟩ = id ,, (t [ id ])

    _⁺ : (σ : Sub Γ Δ) → Sub (Γ ▷ (A [ σ ]T)) (Δ ▷ A)
    σ ⁺ = (σ ∘ p) ,, subst (Tm _) (sym [∘]T) q
  

  module _ (c : CwF-core) where
    open CwF-core c

    record Univ-structure : Set where
      field
        U : Ty Γ
        U[] : U [ σ ]T ≡ U

        El : (t : Tm Γ U) → Ty Γ
        El[] : (El t) [ σ ]T ≡ El (subst (Tm _) U[] (t [ σ ]))

        code : (A : Ty Γ) → Tm Γ U
        code[] : (code A) [ σ ] ≡[ cong (Tm _) U[] ] code (A [ σ ]T)

        El-code : El (code A) ≡ A
        code-El : code (El t) ≡ t

      _[_]U : (t : Tm Δ U) → (σ : Sub Γ Δ) → Tm Γ U
      _[_]U t σ = coeTm U[] (t [ σ ])

      _⁺U : (σ : Sub Γ Δ) → Sub (Γ ▷ El (t [ σ ]U)) (Δ ▷ El t)
      σ ⁺U = ((σ ∘ p) ,, subst (Tm _) (trans (cong (_[ p ]T) (sym El[])) (sym [∘]T)) q)

      TmU : ∀ Γ → Tm Γ U → Set
      TmU Γ t = Tm Γ (El t)

      _[_]u : (a : TmU Δ t) → (σ : Sub Γ Δ) → TmU Γ (t [ σ ]U)
      _[_]u a σ = coeTm El[] (a [ σ ])

      _▷U_ : (Γ : Con) → Tm Γ U → Con
      Γ ▷U t = Γ ▷ El t

    record Π-structure (univ : Univ-structure) : Set where
      open Univ-structure univ
      field
        Π : (t : Tm Γ U) → (u : Tm (Γ ▷U t) U) → Tm Γ U
        Π[] : (Π t u) [ σ ]U ≡ Π (t [ σ ]U) (u [ σ ⁺U ]U)

        lam : (f : TmU (Γ ▷U t) u) → TmU Γ (Π t u)
        lam[] : (lam t) [ σ ]u ≡[ cong (TmU _) Π[] ] lam (t [ σ ⁺U ]u)

        ap : (f : TmU Γ (Π t u)) → TmU (Γ ▷U t) u

        β : ap (lam t) ≡ t
        η : lam (ap t) ≡ t



