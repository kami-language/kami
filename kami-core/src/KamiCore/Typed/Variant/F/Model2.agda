
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model2 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Closure.Exponential.Definition
open import Agora.Category.Std.Limit.Specific.Product.Definition
open import Agora.Category.Std.Limit.Specific.Product.Instance.Functor
open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition

open import Data.Vec hiding ([_] ; map)
open import Data.Fin using (Fin ; suc ; zero)



record MTTꟳ (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field 𝓂 : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:𝓂}} : isCategory {𝑖 ⌄ 1 ⋯ 2} 𝓂
  field {{is2Category:𝓂}} : is2Category {𝑖 ⌄ 3 ⋯ 4} ′ 𝓂 ′

open MTTꟳ {{...}} public

record Model-MTTꟳ 𝑗 {{A : MTTꟳ 𝑖}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field 𝒞 : 𝓂 -> Category 𝑗
  field 𝒟 : CartesianClosedCategory 𝑗
  -- field {{isCartesianClosedCategory:𝒟}} : isCartesianClosedCategory 𝒟
  field {{hasFiniteProducts:𝒞}} : ∀ {m} -> hasFiniteProducts (𝒞 m)
  field embed : ∀ m -> Functor (𝒞 m) (↳ (↳ 𝒟))
  field Modal : ∀{a b : 𝓂} -> a ⟶ b -> Functor (𝒞 a) (𝒞 b)

open Model-MTTꟳ {{...}} public


module Definition-MTTꟳ-Model {{A : MTTꟳ 𝑖}} {{Param : Model-MTTꟳ 𝑗 {{A}}}} where
  private
    𝓂' : Category _
    𝓂' = ′ 𝓂 ′

  ModeHom : (a b : 𝓂) -> 𝒰 _
  ModeHom a b = a ⟶ b

  private variable
    k l m n o p m₀ n₀ m₁ n₁ l₀ l₁ : 𝓂 {{A}}
    μ : Hom {{of 𝓂'}} m n
    μ₀ : Hom {{of 𝓂'}} m n
    μ₁ : Hom {{of 𝓂'}} m n
    ν  : Hom {{of 𝓂'}} m n
    ν₀ : Hom {{of 𝓂'}} m n
    ν₁ : Hom {{of 𝓂'}} m n
    ν₂ : Hom {{of 𝓂'}} m n
    η  : Hom {{of 𝓂'}} m n
    η₀ : Hom {{of 𝓂'}} m n
    η₁ : Hom {{of 𝓂'}} m n
    ω  : Hom {{of 𝓂'}} m n

  data Ctx : (m n : 𝓂) -> 𝒰 (𝑖 ､ 𝑗) where
    ε : Ctx m m
    _∙⟮_∣_⟯ : Ctx k n -> ⟨ 𝒞 m ⟩ -> m ⟶ n -> Ctx k n
    _∙!_ : Ctx k n -> m ⟶ n -> Ctx k m

  infix 32 _∙⟮_∣_⟯
  infixl 30 _∙!_


  -- data _⊢Var⟮_∣_⇒_⟯ : (Γ : Ctx k) (A : ⟨ 𝒞 m ⟩) (μ : m ⟶ l) (η : k ⟶ l) → 𝒰 𝑖 where
  --   zero : ∀{Γ} {μ : m ⟶ l} -> (Γ ∙⟮ A ∣ μ ⟯) ⊢Var⟮ A ∣ μ ⇒ id ⟯
  --   suc! : ∀{Γ} {μ : m ⟶ l} {η : k ⟶ l} {ω : o ⟶ k} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙! ω ⊢Var⟮ A ∣ μ ⇒ ω ◆ η ⟯
  --   suc : Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙⟮ B ∣ ω ⟯ ⊢Var⟮ A ∣ μ ⇒ η ⟯

  ⟦_⟧-Ctx : Ctx m n -> ⟨ 𝒟 ⟩
  ⟦ ε ⟧-Ctx = ⊤
  ⟦ Γ ∙⟮ x ∣ μ ⟯ ⟧-Ctx = ⟦ Γ ⟧-Ctx ⊓ ⟨ embed _ ⟩ (⟨ Modal μ ⟩ x)
  ⟦ Γ ∙! x ⟧-Ctx = ⟦ Γ ⟧-Ctx

  -- target : Ctx k -> 𝓂
  -- target {k} ε = k
  -- target {k} (Γ ∙⟮ x ∣ x₁ ⟯) = target Γ
  -- target {k} (Γ ∙! x) = target Γ

  restr : (Γ : Ctx m n) -> n ⟶ m
  restr ε = id
  restr (Γ ∙⟮ A ∣ α ⟯) = restr Γ
  restr (Γ ∙! α) = α ◆ restr Γ


  size : Ctx m n -> ℕ
  size ε = 0
  size (Γ ∙⟮ x ∣ x₁ ⟯) = suc (size Γ)
  size (Γ ∙! x) = size Γ

  target : (Γ : Ctx m n) -> (i : Fin (size Γ)) -> ⟨ 𝒞 m ⟩
  target (Γ ∙⟮ A ∣ α ⟯) zero = ⟨ Modal (α ◆ restr Γ) ⟩ A
  target (Γ ∙⟮ A ∣ α ⟯) (suc i) = target Γ i
  target (Γ ∙! α) i = target Γ i


  source : (Γ : Ctx m n) -> (i : Fin (size Γ)) -> ⟨ 𝒞 m ⟩
  source (Γ ∙⟮ x ∣ x₁ ⟯) zero = {!!}
  source (Γ ∙⟮ x ∣ x₁ ⟯) (suc i) = {!!}
  source (Γ ∙! x) i = source Γ i

  Fibers : ∀ n -> 𝒰 _
  Fibers n = ∀{a b : 𝓂} -> (α β : a ⟶ b) -> Fin n -> 𝒰 𝑖

  fibers : (β : n ⟶ k) -> (Γ : Ctx l k) -> Fibers (size Γ)
  fibers β ε = λ α β' i -> ⊥-𝒰
  fibers β (Γ ∙⟮ x ∣ α ⟯) = {!!}
  fibers β (Γ ∙! α) = fibers (β ◆ α) Γ

  record SemanticHom (Γ : Ctx m n) (A : ⟨ 𝒞 n ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field vars : Fin (size Γ) -> ℕ
    -- field tran : 
    field term : HomOf (𝒞 m) (⨅ᶠⁱⁿ (λ (i : Fin (size Γ)) -> ⨅ᶠⁱⁿ λ (j : Fin (vars i)) -> target Γ i))
                             (⟨ Modal (restr Γ) ⟩ A)

  -- _⇉_ : ∀{m n} -> (μ ν : m ⟶ n) -> 




