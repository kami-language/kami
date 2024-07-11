

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

--
-- Purpose: Function types don't have modalites,
-- mod introduces always single modalities
--

module KamiCore.Language.MinMTT.Properties where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiCore.Language.MTT.Definition
open import KamiCore.Language.MinMTT.Definition




module Min𝔐TT/Properties (This : Min𝔐TT 𝑖) where
  open Min𝔐TT/Definition This
  open [Min𝔐TT/Definition::Private]
  open [Min𝔐TT/Definition::Type]
  open [Min𝔐TT/Definition::Ctx]
  open [Min𝔐TT/Definition::Term]

  private variable
    a b c d : 𝓂
    X Y : ⊢Type a
    μ μ₀ μ₁ ν η ν₀ ν₁ η' : ModeHom a b


  preserve-◆-Mod-Type : {μ : Path _⟶ₛ_ a b} {ν : Path _⟶ₛ_ b c}
                      -> Mod-Type (μ ◆' ν) A ≡ Mod-Type ν (Mod-Type μ A)
  preserve-◆-Mod-Type {μ = id'} = refl-≡
  preserve-◆-Mod-Type {μ = x ⨾ μ} = preserve-◆-Mod-Type {μ = μ}


  -- transp- : Γ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> Γ ∙! idₛ ⊢Var⟮ X ∣ μ ⇒ η ⟯

  lift-id : Γ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> Γ ∙! idₛ ⊢Var⟮ X ∣ μ ⇒ η ⟯
  lift-id v = {!!}

  lift-id-Term : Γ ⊢ X -> Γ ∙! idₛ ⊢ X
  lift-id-Term = {!!}

  transp-Var-∼ : ν₀ ∼ ν₁ -> Γ ⊢Var⟮ X ∣ μ ⇒∼ ν₀ ⟯ -> Γ ⊢Var⟮ X ∣ μ ⇒∼ ν₁ ⟯
  transp-Var-∼ = {!!}

  transp-Ctx-∼ : μ₀ ∼ μ₁ -> Γ ∙⟮ A ∣ μ₀ ⟯ ⊢ X -> Γ ∙⟮ A ∣ μ₁ ⟯ ⊢ X
  transp-Ctx-∼ = {!!}

  transp-Ctx-res : ∀{μ₀ : Path _⟶ₛ_ a b} {μ₁ : Path _⟶ₛ_ b c} -> ∀{μ} -> μ₀ ◆' μ₁ ≡ μ -> (Γ ∙!* μ₁) ∙!* μ₀ ⊢ X -> (Γ ∙!* μ) ⊢ X
  transp-Ctx-res = {!!}

  transp-Ctx-res2 : ∀{μ₀ : Path _⟶ₛ_ a b} {μ₁ : Path _⟶ₛ_ a b}
                    -> Comp-Path fst μ₀ ∼ Comp-Path fst μ₁
                    -> (Γ ∙!* μ₀) ⊢ X -> Γ ∙!* μ₁ ⊢ X
  transp-Ctx-res2 = {!!}

  transp-Ctx : Γ ≡ Δ -> Γ ⊢ X -> Δ ⊢ X
  transp-Ctx = {!!}

  suc!* : ∀{ωs : Path _⟶ₛ_ d c} {μ : ModeHom a b} {η : ModeHom c b} {X : ⊢Type a}
        -> η' ∼ (Comp-Path fst ωs) ◆ η
        -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
        -> Γ ∙!* ωs ⊢Var⟮ X ∣ μ ⇒ η' ⟯
  suc!* = {!!}

  -- varzero : ∀{μs : Path _⟶ₛ_ a b} -> {X : ⊢Type a} -> {Γ : ⊢Ctx {c} b} -> Γ ∙⟮ X ∣ Comp-Path fst μs ⟯ ∙!* μs ⊢ X
  -- varzero {μs = id'} = var zero {!!} {!!}
  -- varzero {μs = x ⨾ id'} = var (suc! zero) {!!} {!!}
  -- varzero {μs = x ⨾ x₁ ⨾ μs} = {!!}
  -- var (suc!* {!μs!} {!μ!}) {!!} {!!}

  ----------------------------------------------------------
  -- Weakening

  _⋆-Ctx_ : (Γ : ⊢Ctx {a} b) -> ⊢Ctx {b} c -> ⊢Ctx {a} c
  Γ ⋆-Ctx ε = Γ
  Γ ⋆-Ctx (Δ ∙⟮ x ∣ x₁ ⟯) = (Γ ⋆-Ctx Δ) ∙⟮ x ∣ x₁ ⟯
  Γ ⋆-Ctx (Δ ∙! x) = (Γ ⋆-Ctx Δ) ∙! x

  wk-ind : (Γ ⋆-Ctx Δ) ⊢ X -> (Γ ∙⟮ A ∣ μ ⟯ ⋆-Ctx Δ) ⊢ X
  wk-ind = {!!}


  com-∙!* : ∀{νs : Path _⟶ₛ_ a b} -> Γ ⋆-Ctx (ε ∙!* νs) ≡ Γ ∙!* νs
  com-∙!* = {!!}


