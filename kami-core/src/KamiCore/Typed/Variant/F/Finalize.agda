

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
    Unit : LType
    _××_ : LType -> LType -> LType

  data LCtx : 𝒰₀ where
    ε : LCtx
    _,_ : LCtx -> LType -> LCtx

  private variable
    Γ : LCtx
    A B : LType
    X : FType

  data _⊢Var_Locally : LCtx -> LType -> 𝒰₀ where
    zero : Γ , A ⊢Var A Locally
    suc : Γ ⊢Var A Locally -> Γ , B ⊢Var A Locally

  data _⊢_Locally : LCtx -> LType -> 𝒰₀ where
    var : Γ ⊢Var A Locally -> Γ ⊢ A Locally
    lam : Γ , A ⊢ B Locally -> Γ ⊢ A ⇒ B Locally
    box : (∀ n -> Γ ⊢ X n Locally) -> Γ ⊢ ◻ X Locally
    proj : Γ ⊢ ◻ X Locally -> ∀ n -> Γ ⊢ X n Locally
    _,_ : Γ ⊢ A Locally -> Γ ⊢ B Locally -> Γ ⊢ A ×× B Locally
    tt : Γ ⊢ Unit Locally


  FCtx : 𝒰₀
  FCtx = 𝔽 n -> LCtx


  _⊢_Fibered : FCtx -> FType -> 𝒰₀
  _⊢_Fibered Γ X = ∀ n -> Γ n ⊢ X n Locally


  ⟦_⟧-FType : Type ◯ -> FType

  {-# TERMINATING #-}
  ⟦_⟧-LType : Type ▲ -> LType
  ⟦ ◻ T ⟧-LType = ◻ ⟦ T ⟧-FType
  ⟦ [ T ∣ x ]◅ S ⟧-LType = {!!}
  ⟦ T ∥ S ⟧-LType = ⟦ T ⟧-LType ×× ⟦ S ⟧-LType
  ⟦ NN ⟧-LType = {!!}
  ⟦ Unit ⟧-LType = Unit
  ⟦ Either T S ⟧-LType = {!!}
  ⟦ T ⇒ S ⟧-LType = ⟦ T ⟧-LType ⇒ ⟦ S ⟧-LType
  ⟦ T ×× S ⟧-LType = {!!}
  ⟦ Tr T ⟧-LType = {!!}

  ⟦_⟧-FType X n = ⟦ π-Type X (⦗ n ⦘ , []) ⟧-LType

  ⟦_⟧-LCtx : ∀ {Δ : Ctx'} -> ∀{p} -> isLocal p Δ -> LCtx
  ⟦_⟧-LCtx ε = ε
  ⟦_⟧-LCtx (P , A) = ⟦ P ⟧-LCtx , ⟦ A ⟧-LType
  ⟦_⟧-LCtx (stepRes P) = ⟦ P ⟧-LCtx

  ⟦_⟧-FCtx : ∀ (Γ : Ctx') -> FCtx
  ⟦_⟧-FCtx Γ n = ⟦ local-Proof (π-Ctx-Proof Γ (⦗ n ⦘ ∷ [])) ⟧-LCtx



  wk : Γ ⊢ A Locally -> Γ , B ⊢ A Locally
  wk = {!!}

  tπ : ∀{X B p ps} -> π X ∣ p , ps ↦ B Type -> Γ ⊢ ⟦ ◻ X ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tπ (proj-＠ x x₁) t = {!!}
  tπ (proj-＠-≠ x) t = tt
  tπ (p ⇒ p₁) t = {!!}
  tπ (p ×× p₁) t = {!!}
  tπ (Either p p₁) t = {!!}
  tπ (Tr p) t = {!!}
  tπ Unit t = {!!}

  tω : ∀{A B ps} -> ω A ∣ ps ↦ B Type -> Γ ⊢ ⟦ A ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tω done t = t
  tω (proj-◻ p x) t = tω p t , tπ x t
  tω Unit t = t

  tϕ : ∀{A B} -> ϕ A ↦ B -> Γ ⊢ ⟦ A ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tϕ = {!!}

  tv  : ∀{Δ A p ps} -> (Δp : isLocal p Δ) -> Δ ⊢Var A GlobalFiber[ p ∷ ps ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tv (Δp IR., A) (IR.zero (IR.proj-＠ x x₂) x₁) = tϕ x₁ (tω x₂ (var zero))
  tv (Δp , A) (IR.suc v) = let x = tv Δp v in wk x
  tv (IR.stepRes Δp) (IR.res v) = let x = tv Δp v in x


  ta : ∀ {Γ X} -> Γ ⊢ X GlobalFibered[ All ] -> ⟦ Γ ⟧-FCtx ⊢ ⟦ X ⟧-FType Fibered

  -- tr : ∀ {Γ Δ p A} -> (Δp : Γ ∣ ⦗ p ⦘ ∷ [] ↦ Δ Ctx) -> Δ ⊢ A GlobalFiber[ p ] -> ⟦ local-Proof Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally

  tr : ∀ {Δ p A} -> (Δp : isLocal ⦗ p ⦘ Δ) -> Δ ⊢ A GlobalFiber[ p ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tr Δp (var v) = tv Δp v
  tr Δp (recv x) = {!!}
  tr Δp (send v t) = {!!}
  tr Δp (extern t) = {!!} -- tr {!stepRes Δp!} t
  tr {p = p} Δp (lam {A = A} {B = B} t) =
    let t' = tr (Δp , {!!}) t
    in lam t'
  tr Δp (app t t₁) = {!!}
  tr Δp tt = {!!}
  tr Δp (box x x₁) = {!!}
  tr {Δ} Δp (box' x) =
    let t' = ta {Γ = Δ ,[ _ ]} x
    in box {!t'!} -- Δ is already projected to p, so Δ ,[ p ] projected should become again Δ

  ta {Γ = Γ} {X} ts n = tr (local-Proof (π-Ctx-Proof Γ _)) (⟨ ts ⟩ n {!!} (π-Type-Proof X {!!} _) (π-Ctx-Proof Γ _))




