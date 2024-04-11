
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.I.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∙_ ; _∣_)
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition

-- open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
-- open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition -- hiding (_◆_)
-- open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition


record MTTᴵ (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field 𝓂 : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:𝓂}} : isCategory {𝑖 ⌄ 1 ⋯ 2} 𝓂
  field {{is2Category:𝓂}} : is2Category {𝑖 ⌄ 3 ⋯ 4} ′ 𝓂 ′

open MTTᴵ {{...}} public


module Definition-MTTᴵ {𝑖 : 𝔏 ^ 5} {{Param : MTTᴵ 𝑖}} where
  private
    𝓂' : Category _
    𝓂' = ′ 𝓂 ′

  private variable
    k l m n o p : 𝓂 {{Param}}
    μ : Hom {{of 𝓂'}} m n
    ν : Hom {{of 𝓂'}} n o
    η : Hom {{of 𝓂'}} o k
    ω : Hom {{of 𝓂'}} n o


  data ⊢Type : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    ⟨_∣_⟩ : ⊢Type m -> m ⟶ n -> ⊢Type n
    Unit : ⊢Type m
    ⟮_∣_⟯⇒_ : ⊢Type m -> m ⟶ n -> ⊢Type n -> ⊢Type n

  infix 30 ⟨_∣_⟩ ⟮_∣_⟯⇒_

  private variable
    A : ⊢Type m
    B : ⊢Type n

  data Restriction : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    [] : Restriction k
    _∷_ : k ⟶ l -> Restriction l -> Restriction k

  private variable
    M : Restriction k
    N : Restriction k

  -- Given a restriction with domain k, we can precompose
  -- the first modality with a morphism (μ : l → k) to get
  -- a restriction with domain l.
  --
  -- This is the operation denoted by Γ.{μ} in MTT.
  --
  _↳_ : l ⟶ k -> Restriction k -> Restriction l
  μ ↳ [] = []
  μ ↳ (x ∷ M) = μ ◆ x ∷ M

  data TypeCtx : (m : 𝓂) -> (M : Restriction m) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    ε : TypeCtx m []
    _∙⟮_∣_⟯ : TypeCtx n M -> ⊢Type m -> (μ : m ⟶ n) -> {η : k ⟶ n} -> TypeCtx k (η ∷ M)
    -- _∙!_ : Ctx n -> m ⟶ n -> Ctx m


  infixl 32 _∙⟮_∣_⟯
  -- infixl 30 _∙!_

  record Ctx (m : 𝓂) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    constructor ctx
    field restr : Restriction m
    field types : TypeCtx m restr

  open Ctx public

  syntax ctx b a = a / b

  pattern _∙⟮_∣_⇒_⟯/_ Γ A μ η M = Γ ∙⟮ A ∣ μ ⟯ / (η ∷ M)
  -- : TypeCtx n M -> ⊢Type m -> (μ : m ⟶ n) -> {η : k ⟶ n} -> TypeCtx k (η ∷ M)

  -- _∙⟮_∣_⟯ : Ctx n -> ⊢Type m -> m ⟶ n -> Ctx n
  -- _∙⟮_∣_⟯ (Γ / M) A μ = Γ ∙⟮ A ∣ μ ⇒ id ⟯/ M

  private variable
    Γ : Ctx m
    Δ : Ctx n

-- (M : Restriction k n) 
  data _⊢Var⟮_∣_⇒_⟯ : (Γ : Ctx k) (A : ⊢Type m) (μ : m ⟶ l) (η : k ⟶ l) → 𝒰 𝑖 where
    zero : ∀{Γ} -> (Γ ∙⟮ A ∣ μ ⇒ η ⟯/ M) ⊢Var⟮ A ∣ μ ⇒ η ⟯
    suc  : ∀{M Γ}
         -> {μ : m ⟶ l}
         -> {η : k ⟶ l}
         -> {ν : o ⟶ _}
         -> {ω : p ⟶ _}
         -> (h : (Γ / M) ⊢Var⟮ A ∣ μ ⇒ η ⟯)
         -> (Γ ∙⟮ B ∣ ν ⇒ ω ⟯/ M) ⊢Var⟮ A ∣ μ ⇒ ω ◆ η ⟯

  data _⊢_ : Ctx m -> ⊢Type m -> 𝒰 𝑖 where
    var : ∀{μ : k ⟶ o} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
    tt : Γ ⊢ Unit
{-
    mod : Γ ∙! μ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩
    letmod : ∀{μ : m ⟶ n} {ν : n ⟶ o}
           -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⟩
           -> Γ ∙⟮ A ∣ μ ◆ ν ⟯ ⊢ B
           -> Γ ⊢ B
    lam : Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
    app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ B -> Γ ⊢ B

  data _⟼_ : Ctx m -> Ctx m -> 𝒰 𝑖 where
    id-Ctx : Γ ⟼ Γ
    _∙‼_ : ∀ Γ -> {μ ν : m ⟶ n} -> μ ⟹ ν -> Γ ∙! ν ⟼ Γ ∙! μ
    _∙!_ : Γ ⟼ Δ -> Γ ∙! μ ⟼ Δ ∙! μ
    _∙⟮_∣_⟯ : Γ ⟼ Δ -> Γ ∙! μ ⊢ A -> Γ ⟼ Δ ∙⟮ A ∣ μ ⟯

-}


open import Agora.TypeTheory.Notation
