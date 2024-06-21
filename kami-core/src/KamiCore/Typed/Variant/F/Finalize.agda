

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Finalize where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)


module Finalize (n : ℕ) where
  -- Instantiating the target language with the preorder
  open import KamiCore.Typed.Variant.F.Model8

  ρ : isProcessSet _
  ρ = record { Proc = 𝔽 n }

  All : 𝒫ᶠⁱⁿ (Proc ρ)
  All = {!!}

  open IR {{ρ}}
    renaming (Ctx to Ctx' ; Mode to Mode')

  data LType : 𝒰₀

  FType : 𝒰₀
  FType = 𝔽 n -> LType

  data LType where
    _⇒_ : LType -> LType -> LType
    ◻ : FType -> LType

  data LCtx : 𝒰₀ where
    ε : LCtx
    _,_ : LCtx -> LType -> LCtx

  private variable
    Γ : LCtx
    A B : LType
    X : FType

  data _⊢_Locally : LCtx -> LType -> 𝒰₀ where
    lam : Γ , A ⊢ B Locally -> Γ ⊢ A ⇒ B Locally
    box : (∀ n -> Γ ⊢ X n Locally) -> Γ ⊢ ◻ X Locally


  FCtx : 𝒰₀
  FCtx = 𝔽 n -> LCtx


  _⊢_Fibered : FCtx -> FType -> 𝒰₀
  _⊢_Fibered Γ X = ∀ n -> Γ n ⊢ X n Locally


  ⟦_⟧-FType : Type ◯ -> FType

  {-# TERMINATING #-}
  ⟦_⟧-LType : Type ▲ -> LType
  ⟦ ◻ T ⟧-LType = ◻ ⟦ T ⟧-FType
  ⟦ [ T ∣ x ]◅ S ⟧-LType = {!!}
  ⟦ T ∥ S ⟧-LType = {!!}
  ⟦ NN ⟧-LType = {!!}
  ⟦ Unit ⟧-LType = {!!}
  ⟦ Either T S ⟧-LType = {!!}
  ⟦ T ⇒ S ⟧-LType = ⟦ T ⟧-LType ⇒ ⟦ S ⟧-LType
  ⟦ T ×× S ⟧-LType = {!!}
  ⟦ Tr T ⟧-LType = {!!}

  ⟦_⟧-FType X n = ⟦ π-Type X (⦗ n ⦘ , []) ⟧-LType

  ⟦_⟧-LCtx : ∀ {Γ} -> {Δ : Ctx'} -> ∀{ps} -> Γ ∣ ps ↦ Δ Ctx -> LCtx
  ⟦_⟧-LCtx ε = ε
  ⟦_⟧-LCtx (_,_ {A = A} P x) = ⟦ P ⟧-LCtx , ⟦ A ⟧-LType
  ⟦_⟧-LCtx (stepRes P) = ⟦ P ⟧-LCtx

  ⟦_⟧-FCtx : ∀ (Γ : Ctx') -> FCtx
  ⟦_⟧-FCtx Γ n = ⟦ (π-Ctx-Proof Γ (⦗ n ⦘ ∷ [])) ⟧-LCtx



  ta : ∀ {Γ X} -> Γ ⊢ X GlobalFibered[ All ] -> ⟦ Γ ⟧-FCtx ⊢ ⟦ X ⟧-FType Fibered

  tr : ∀ {Γ Δ p A} -> (Δp : Γ ∣ ⦗ p ⦘ ∷ [] ↦ Δ Ctx) -> Δ ⊢ A GlobalFiber[ p ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tr Δp (var v) = {!!}
  tr Δp (recv x) = {!!}
  tr Δp (send v t) = {!!}
  tr Δp (extern t) = {!!} -- tr {!stepRes Δp!} t
  tr {p = p} Δp (lam {A = A} {B = B} t) =
    let t' = tr (Δp , proj-＠ refl-≤ done) t
    in lam t'
  tr Δp (app t t₁) = {!!}
  tr Δp tt = {!!}
  tr Δp (box x x₁) = {!!}
  tr {Γ = Γ} {Δ} Δp (box' x) =
    let t' = ta {Γ = Δ ,[ _ ]} x
    in box {!t'!} -- Δ is already projected to p, so Δ ,[ p ] projected should become again Δ

  ta {Γ = Γ} {X} ts n = tr (π-Ctx-Proof Γ _) (⟨ ts ⟩ n {!!} (π-Type-Proof X {!!} _) (π-Ctx-Proof Γ _))




