-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

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
open import Agora.Category.Std.Category.Structured.Classified.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id') hiding (unit-r-◆)

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
    Γ₀ Γ₁ : ⊢Ctx {a} b


  preserve-◆-Mod-Type : {μ : Path _⟶ₛ_ a b} {ν : Path _⟶ₛ_ b c}
                      -> Mod-Type (μ ◆' ν) A ≡ Mod-Type ν (Mod-Type μ A)
  preserve-◆-Mod-Type {μ = id'} = refl-≡
  preserve-◆-Mod-Type {μ = x ⨾ μ} = preserve-◆-Mod-Type {μ = μ}


  -- transp- : Γ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> Γ ∙! idₛ ⊢Var⟮ X ∣ μ ⇒ η ⟯



  _⋆-Ctx_ : (Γ : ⊢Ctx {a} b) -> ⊢Ctx {b} c -> ⊢Ctx {a} c
  Γ ⋆-Ctx ε = Γ
  Γ ⋆-Ctx (Δ ∙⟮ x ∣ x₁ ⟯) = (Γ ⋆-Ctx Δ) ∙⟮ x ∣ x₁ ⟯
  Γ ⋆-Ctx (Δ ∙! x) = (Γ ⋆-Ctx Δ) ∙! x

  infixl 25 _⋆-Ctx_

  transp-Ctx : Γ ≡ Δ -> Γ ⊢ X -> Δ ⊢ X
  transp-Ctx refl-≡ t = t

  com-∙!* : ∀{νs : Path _⟶ₛ_ a b} -> Γ ⋆-Ctx (ε ∙!* νs) ≡ Γ ∙!* νs
  com-∙!* {νs = id'} = refl-≡
  com-∙!* {νs = x ⨾ νs} = cong-≡ (_∙! x) (com-∙!* {νs = νs})

  com2-∙!* : ∀{νs : Path _⟶ₛ_ a b} -> Γ ⋆-Ctx (Δ ∙!* νs) ≡ (Γ ⋆-Ctx Δ) ∙!* νs
  com2-∙!* {νs = id'} = refl-≡
  com2-∙!* {νs = x ⨾ νs} = cong-≡ (_∙! x) (com2-∙!* {νs = νs})


  {-# TERMINATING #-}
  rename-ind : (∀{a b c X Δ} -> {μ : ModeHom a c} -> {ν : ModeHom b c} -> (Γ₀ ⋆-Ctx Δ) ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> Γ₁ ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ∼⇒∼ ν ⟯) -> Γ₀ ⋆-Ctx Δ ⊢ Y -> Γ₁ ⋆-Ctx Δ ⊢ Y
  rename-ind ρ (var x α x₁) =
    let varOver v' p q = ρ x
    in var v' (⟨ 2celliso (sym q) ⟩ ◆ α ◆ ⟨ 2celliso p ⟩) ((preserve-◆ (⟨ 2celliso (sym q) ⟩ ◆ α) ⟨ 2celliso p ⟩
                                                          ⟡-∼≤ [
                                                               preserve-◆ ⟨ 2celliso (sym q) ⟩ α ⟡-∼≤ [ is⊥:2celliso This (sym q) ⟡-∼≤ initial-⊥ , x₁ ]-∨
                                                               , is⊥:2celliso This p ⟡-∼≤ initial-⊥
                                                               ]-∨))
  rename-ind ρ tt = tt
  rename-ind ρ (mod μ t) = mod μ (rename-ind ρ t)
  rename-ind {Δ = Δ} ρ (letmod ν t t₁) = letmod ν (transp-Ctx ((com2-∙!* {Δ = Δ})) (rename-ind ρ (transp-Ctx (sym-≡ (com2-∙!* {Δ = Δ})) t))) (rename-ind ρ t₁)
  rename-ind ρ (trans α x t) = trans α x (rename-ind ρ t)
  rename-ind ρ (pure t) = pure (rename-ind ρ t)
  rename-ind ρ (seq t t₁) = seq (rename-ind ρ t) (rename-ind ρ t₁)
  rename-ind ρ (lam t) = lam (rename-ind ρ t)
  rename-ind ρ (app t t₁) = app (rename-ind ρ t) (rename-ind ρ t₁)
  rename-ind ρ (left t) = left (rename-ind ρ t)
  rename-ind ρ (right t) = right (rename-ind ρ t)
  rename-ind ρ (either t t₁ t₂) = either (rename-ind ρ t) (rename-ind ρ t₁) (rename-ind ρ t₂)
  rename-ind ρ [] = []
  rename-ind ρ (t ∷ t₁) = (rename-ind ρ t) ∷ (rename-ind ρ t₁)
  rename-ind ρ (rec-Lst t t₁ t₂) = rec-Lst (rename-ind ρ t) (rename-ind ρ t₁) (rename-ind ρ t₂)

  lift-id-Var : Γ ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> (Γ ∙! idₛ) ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ∼⇒∼ ν ⟯
  lift-id-Var {Δ = ε} v = varOver (suc! v) (sym unit-l-◆) refl-∼
  lift-id-Var {Δ = Δ ∙⟮ x ∣ x₁ ⟯} zero = varOver zero refl-∼ refl-∼
  lift-id-Var {Δ = Δ ∙⟮ x ∣ x₁ ⟯} (suc v) =
    let varOver v' p' q' = lift-id-Var {Δ = Δ} v
    in varOver (suc v') p' q'
  lift-id-Var {Δ = Δ ∙! x} (suc! v) =
    let varOver v' p' q' = lift-id-Var {Δ = Δ} v
    in varOver (suc! v') (refl-∼ ◈ p') q'


  lift-id : Γ ⊢ X -> Γ ∙! idₛ ⊢ X
  lift-id {Γ = Γ} = rename-ind {Δ = ε} (lift-id-Var {Γ = Γ} )


  transp-Var-∼ : ν₀ ∼ ν₁ -> Γ ⊢Var⟮ X ∣ μ ⇒∼ ν₀ ⟯ -> Γ ⊢Var⟮ X ∣ μ ⇒∼ ν₁ ⟯
  transp-Var-∼ r (varOver v p q) = varOver v p (sym r ∙ q)

  transp2-Var-∼ : μ₀ ∼ μ₁ -> (Γ ∙⟮ A ∣ μ₀ ⟯) ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> (Γ ∙⟮ A ∣ μ₁ ⟯) ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ∼⇒∼ ν ⟯
  transp2-Var-∼ {Δ = ε} r zero = varOver zero refl-∼ r
  transp2-Var-∼ {Δ = ε} r (suc v) = varOver (suc v) refl-∼ refl-∼
  transp2-Var-∼ {Δ = Δ ∙⟮ x ∣ x₁ ⟯} r zero = varOver zero refl-∼ refl-∼
  transp2-Var-∼ {Δ = Δ ∙⟮ x ∣ x₁ ⟯} r (suc v) =
    let varOver v' p' q' = transp2-Var-∼ {Δ = Δ} r v
    in varOver (suc v') p' q'
  transp2-Var-∼ {Δ = Δ ∙! x} r (suc! v) =
    let varOver v' p' q' = transp2-Var-∼ {Δ = Δ} r v
    in varOver (suc! v') (refl-∼ ◈ p') q'

  transp-Ctx-∼ : μ₀ ∼ μ₁ -> Γ ∙⟮ A ∣ μ₀ ⟯ ⊢ X -> Γ ∙⟮ A ∣ μ₁ ⟯ ⊢ X
  transp-Ctx-∼ {A = A} p = rename-ind {Δ = ε} (λ v -> transp2-Var-∼ {A = A} p v)

  -- transp-Ctx-res : ∀{μ₀ : Path _⟶ₛ_ a b} {μ₁ : Path _⟶ₛ_ b c} -> ∀{μ} -> μ₀ ◆' μ₁ ≡ μ -> (Γ ∙!* μ₁) ∙!* μ₀ ⊢ X -> (Γ ∙!* μ) ⊢ X
  -- transp-Ctx-res = {!!}

  suc!*⁻¹ : ∀{μ₀ : Path _⟶ₛ_ a b} {μ : ModeHom c d} -> Γ ∙!* μ₀ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> ∑ λ ν' -> Γ ⊢Var⟮ X ∣ μ ⇒ ν' ⟯ ×-𝒰 Comp-Path fst μ₀ ◆ ν' ∼ ν
  suc!*⁻¹ {μ₀ = id'} v = _ , v , unit-l-◆
  suc!*⁻¹ {μ₀ = x ⨾ μ₀} (suc! v) =
    let _ , v' , p = suc!*⁻¹ {μ₀ = μ₀} v
    in _ , v' , assoc-l-◆ ∙ (refl-∼ ◈ p)

  suc₃!* : ∀{ωs : Path _⟶ₛ_ d c} {μ : ModeHom a b} {η : ModeHom c b} {X : ⊢Type a}
        -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
        -> Γ ∙!* ωs ⊢Var⟮ X ∣ μ ∼⇒∼ (Comp-Path fst ωs) ◆ η ⟯
  suc₃!* {ωs = id'} v = varOver v unit-l-◆ refl-∼ -- (r ∙ unit-l-◆) refl-∼
  suc₃!* {ωs = x ⨾ ωs} v =
    let varOver v' p q = suc₃!* {ωs = ωs} v
    in varOver (suc! v') (assoc-l-◆ ∙ (refl-∼ ◈ p)) q


  -- suc!* : ∀{ωs : Path _⟶ₛ_ d c} {μ : ModeHom a b} {η : ModeHom c b} {X : ⊢Type a}
  --       -> η' ∼ (Comp-Path fst ωs) ◆ η
  --       -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
  --       -> Γ ∙!* ωs ⊢Var⟮ X ∣ μ ⇒∼ η' ⟯

  -- suc!* : ∀{ωs : Path _⟶ₛ_ d c} {μ : ModeHom a b} {η : ModeHom c b} {X : ⊢Type a}
  --       -> η' ∼ (Comp-Path fst ωs) ◆ η
  --       -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
  --       -> Γ ∙!* ωs ⊢Var⟮ X ∣ μ ∼⇒∼ split This (Comp-Path fst ωs ◆ η) ⟯
  -- suc!* {ωs = ωs} r v = {!!}



  transp-Ctx-res2-Var : ∀{μ₀ : Path _⟶ₛ_ a b} {μ₁ : Path _⟶ₛ_ a b}
                    -> Comp-Path fst μ₀ ∼ Comp-Path fst μ₁
                    -> (Γ ∙!* μ₀) ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> (Γ ∙!* μ₁) ⋆-Ctx Δ ⊢Var⟮ X ∣ μ ∼⇒∼ ν ⟯
  transp-Ctx-res2-Var {Δ = ε} {μ₀ = μ₀} {μ₁ = μ₁} r v =
    let _ , v' , p = suc!*⁻¹ {μ₀ = μ₀} v
        varOver v'' p'' q'' = (suc₃!* {ωs = μ₁}  v')
    in varOver v'' (sym p ∙ r ◈ refl-∼ ∙ p'') q'' -- (sym p ∙ r ◈ refl-∼)
    -- varOver  refl-∼ refl-∼
    -- {!!} -- varOver zero refl-∼ r
  -- transp-Ctx-res2-Var {Δ = ε} r (suc v) = varOver (suc v) refl-∼ refl-∼
  transp-Ctx-res2-Var {Δ = Δ ∙⟮ x ∣ x₁ ⟯} r zero = varOver zero refl-∼ refl-∼
  transp-Ctx-res2-Var {Δ = Δ ∙⟮ x ∣ x₁ ⟯} {μ₀ = μ₀} {μ₁ = μ₁} r (suc v) =
    let varOver v' p' q' = transp-Ctx-res2-Var {Δ = Δ} {μ₀ = μ₀} r v
    in varOver (suc v') p' q'
  transp-Ctx-res2-Var {Δ = Δ ∙! x} {μ₀ = μ₀} r (suc! v) =
    let varOver v' p' q' = transp-Ctx-res2-Var {Δ = Δ} {μ₀ = μ₀} r v
    in varOver (suc! v') (refl-∼ ◈ p') q'


  transp-Ctx-res2 : ∀{μ₀ : Path _⟶ₛ_ a b} {μ₁ : Path _⟶ₛ_ a b}
                    -> Comp-Path fst μ₀ ∼ Comp-Path fst μ₁
                    -> (Γ ∙!* μ₀) ⊢ X -> Γ ∙!* μ₁ ⊢ X
  transp-Ctx-res2 {Γ = Γ} {μ₀ = μ₀} {μ₁ = μ₁} p = rename-ind {Δ = ε} (transp-Ctx-res2-Var {Γ = Γ} {μ₀ = μ₀} {μ₁ = μ₁} p)

  -- suc!* : ∀{ωs : Path _⟶ₛ_ d c} {μ : ModeHom a b} {η : ModeHom c b} {X : ⊢Type a}
  --       -> η' ∼ (Comp-Path fst ωs) ◆ η
  --       -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
  --       -> Γ ∙!* ωs ⊢Var⟮ X ∣ μ ⇒ η' ⟯
  -- suc!* = {!!}

  -- varzero : ∀{μs : Path _⟶ₛ_ a b} -> {X : ⊢Type a} -> {Γ : ⊢Ctx {c} b} -> Γ ∙⟮ X ∣ Comp-Path fst μs ⟯ ∙!* μs ⊢ X
  -- varzero {μs = id'} = var zero {!!} {!!}
  -- varzero {μs = x ⨾ id'} = var (suc! zero) {!!} {!!}
  -- varzero {μs = x ⨾ x₁ ⨾ μs} = {!!}
  -- var (suc!* {!μs!} {!μ!}) {!!} {!!}

  ----------------------------------------------------------
  -- Weakening

  wk-Var : (Γ ⋆-Ctx Δ) ⊢Var⟮ X ∣ μ ⇒ ν ⟯ -> (Γ ∙⟮ A ∣ η ⟯ ⋆-Ctx Δ) ⊢Var⟮ X ∣ μ ⇒ ν ⟯
  wk-Var {Δ = ε} v = suc v
  wk-Var {Δ = Δ ∙⟮ x ∣ x₁ ⟯} zero = zero
  wk-Var {Δ = Δ ∙⟮ x ∣ x₁ ⟯} (suc v) = suc (wk-Var v)
  wk-Var {Δ = Δ ∙! x} (suc! v) = suc! (wk-Var v)

  {-# TERMINATING #-}
  wk-ind : (Γ ⋆-Ctx Δ) ⊢ X -> (Γ ∙⟮ A ∣ μ ⟯ ⋆-Ctx Δ) ⊢ X
  wk-ind (var x α x₁) = var (wk-Var x) α x₁
  wk-ind tt = tt
  wk-ind (mod μ t) = mod μ (wk-ind t)
  wk-ind {Δ = Δ} (letmod ν t t₁) = letmod ν ((transp-Ctx ((com2-∙!* {Δ = Δ})) (wk-ind (transp-Ctx (sym-≡ (com2-∙!* {Δ = Δ})) t)))) (wk-ind {Δ = Δ ∙⟮ _ ∣ _ ⟯} t₁)
  wk-ind (trans α x t) = trans α x (wk-ind t)
  wk-ind (pure t) = pure (wk-ind t)
  wk-ind {Δ = Δ} (seq t t₁) = seq (wk-ind t) (wk-ind {Δ = Δ ∙⟮ _ ∣ _ ⟯} t₁)
  wk-ind {Δ = Δ} (lam t) = lam (wk-ind {Δ = Δ ∙⟮ _ ∣ _ ⟯} t)
  wk-ind (app t t₁) = app (wk-ind t) (wk-ind t₁)
  wk-ind (left t) = left (wk-ind t)
  wk-ind (right t) = right (wk-ind t)
  wk-ind {Δ = Δ} (either t t₁ t₂) = either (wk-ind t) (wk-ind {Δ = Δ ∙⟮ _ ∣ _ ⟯} t₁) (wk-ind {Δ = Δ ∙⟮ _ ∣ _ ⟯} t₂)
  wk-ind [] = []
  wk-ind (t ∷ t₁) = (wk-ind t) ∷ (wk-ind t₁)
  wk-ind {Δ = Δ} (rec-Lst t t₁ t₂) = rec-Lst (wk-ind t) (wk-ind t₁) (wk-ind {Δ = Δ ∙⟮ _ ∣ _ ⟯ ∙⟮ _ ∣ _ ⟯} t₂)




