
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
open import Agora.Category.Std.Limit.Specific.Product.Variant.Indexed
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Data.Fin.Definition
open import Agora.Data.FinSet.Definition

open import Data.Vec hiding ([_] ; map ; length)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Nat using (_+_ ; _*_)



record MTTꟳ (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field 𝓂 : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:𝓂}} : isCategory {𝑖 ⌄ 1 ⋯ 2} 𝓂
  field {{is2Category:𝓂}} : is2Category {𝑖 ⌄ 3 ⋯ 4} ′ 𝓂 ′

open MTTꟳ {{...}} public

record Model-MTTꟳ 𝑗 {{A : MTTꟳ 𝑖}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field 𝒞 : 𝓂 -> Category 𝑗
  𝒞Obj : 𝓂 -> 𝒰 _
  𝒞Obj m = ⟨ 𝒞 m ⟩

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
    k l m n o p m₀ n₀ m₁ n₁ n₂ l₀ l₁ : 𝓂 {{A}}
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

  private variable
    Γ : Ctx m n

  data ⟮_∣_⇒_⟯∈_ {m l} (A : ⟨ 𝒞 m ⟩) (μ : m ⟶ l) : (η : k ⟶ l) (Γ : Ctx o k) → 𝒰 (𝑖 ､ 𝑗) where
    zero : ∀{Γ : Ctx o l} -> ⟮ A ∣ μ ⇒ idOn l ⟯∈ (Γ ∙⟮ A ∣ μ ⟯)
    suc! : ∀{Γ : Ctx o k} {η : k ⟶ l} {ω : o ⟶ k} -> ⟮ A ∣ μ ⇒ η ⟯∈ Γ -> ⟮ A ∣ μ ⇒ ω ◆ η ⟯∈ Γ ∙! ω
    suc : ∀{B} -> ⟮ A ∣ μ ⇒ η ⟯∈ Γ -> ⟮ A ∣ μ ⇒ η ⟯∈ Γ ∙⟮ B ∣ ω ⟯

  record Varᵘ (Γ : Ctx o k) : 𝒰 (𝑖 ､ 𝑗) where
    field origin : 𝓂
    field current : 𝓂
    field source : origin ⟶ current
    field target : origin ⟶ current
    field type : ⟨ 𝒞 origin ⟩

  open Varᵘ public

  instance
    isFinite:Var : isFinite (Varᵘ Γ)
    isFinite:Var = record { size = {!!} ; index = {!!} ; isIso:index = {!!} }

  module _ (Γ : Ctx o k) where
    macro Var = #structureOn (Varᵘ Γ)


  ⟦_⟧-Ctx : Ctx m n -> ⟨ 𝒟 ⟩
  ⟦ ε ⟧-Ctx = ⊤
  ⟦ Γ ∙⟮ x ∣ μ ⟯ ⟧-Ctx = ⟦ Γ ⟧-Ctx ⊓ ⟨ embed _ ⟩ (⟨ Modal μ ⟩ x)
  ⟦ Γ ∙! x ⟧-Ctx = ⟦ Γ ⟧-Ctx

  -- source : Ctx k -> 𝓂
  -- source {k} ε = k
  -- source {k} (Γ ∙⟮ x ∣ x₁ ⟯) = source Γ
  -- source {k} (Γ ∙! x) = source Γ

  restr : (Γ : Ctx m n) -> n ⟶ m
  restr ε = id
  restr (Γ ∙⟮ A ∣ α ⟯) = restr Γ
  restr (Γ ∙! α) = α ◆ restr Γ


  length : Ctx m n -> ℕ
  length ε = 0
  length (Γ ∙⟮ x ∣ x₁ ⟯) = suc (length Γ)
  length (Γ ∙! x) = length Γ

  modal∂ : (Γ : Ctx m n) -> (i : Fin (length Γ)) -> 𝓂 × 𝓂
  modal∂ {n = n} (_∙⟮_∣_⟯ {m = m} Γ x α) zero = m , n
  modal∂ (Γ ∙⟮ x ∣ x₁ ⟯) (suc i) = modal∂ Γ i
  modal∂ (Γ ∙! x) i = modal∂ Γ i

  
{-
  source : (Γ : Ctx m n) -> (i : Fin (length Γ)) -> ⟨ 𝒞 m ⟩
  source (Γ ∙⟮ A ∣ α ⟯) zero = ⟨ Modal (α ◆ restr Γ) ⟩ A
  source (Γ ∙⟮ A ∣ α ⟯) (suc i) = source Γ i
  source (Γ ∙! α) i = source Γ i

  target : (Γ : Ctx m n) -> (i : Fin (length Γ)) -> fst (modal∂ Γ i) ⟶ n -> ⟨ 𝒞 m ⟩
  target (Γ ∙⟮ A ∣ x₁ ⟯) zero β = ⟨ Modal (β ◆ restr Γ) ⟩ A
  target (Γ ∙⟮ A ∣ x₁ ⟯) (suc i) p = target Γ i p
  target (Γ ∙! α) i β = target Γ i (β ◆ α)
  -}


  -- cut-Ind : (Γ : Ctx m n) -> (v : Γ ) -> Ctx m (current v)

  cut : (Γ : Ctx m n) -> (v : Var Γ) -> Ctx m (current v)
  cut Γ = {!!}


  lo : (Γ : Ctx m n) -> Var Γ -> ⟨ 𝒞 m ⟩
  lo Γ v = {!!}

  Fibers : ∀ n -> 𝒰 _
  Fibers n = ∀{a b : 𝓂} -> (α β : a ⟶ b) -> Fin n -> 𝒰 𝑖

  fibers : (β : n ⟶ k) -> (Γ : Ctx l k) -> Fibers (length Γ)
  fibers β ε = λ α β' i -> ⊥-𝒰
  fibers β (Γ ∙⟮ x ∣ α ⟯) = {!!}
  fibers β (Γ ∙! α) = fibers (β ◆ α) Γ

  record SemanticHom (Γ : Ctx m n) (A : 𝒞Obj n) : 𝒰 (𝑖 ､ 𝑗 ､ ℓ₀ ⁺) where
    constructor semanticHom
    field vars : Var Γ -> 𝐅𝐢𝐧𝐒𝐞𝐭 ℓ₀
    field γ : ∀ x -> ∀ (i : ⟨ vars x ⟩) -> origin x ⟶ n
    -- field tran : ∀ x -> ∀(i : ⟨ vars i ⟩) -> HomOf (𝒞 _) (source Γ i) (target Γ i (goodVars i j))
    field term : HomOf (𝒞 m) (⨅[ x ∶ Var Γ ] ⨅[ i ∶ vars x ] {!!}) {!!}
    -- field γ : ∀ x -> ∀ (i : ⟨ vars x ⟩) -> fst (modal∂ Γ i) ⟶ n
    -- field tran : ∀ i -> ∀(j : Fin (vars i)) -> HomOf (𝒞 _) (source Γ i) (target Γ i (goodVars i j))
    -- field term : HomOf (𝒞 m) (⨅ᶠⁱⁿ i ∈ length Γ , ⨅ᶠⁱⁿ j ∈ vars i , target Γ i (goodVars i j))
    --                          (⟨ Modal (restr Γ) ⟩ A)

  open SemanticHom public

{-

  -- target : (β : l ⟶ n) -> (Γ : Ctx m n) -> (i : Fin (length Γ)) -> fst (modal∂ Γ i) ⟶ n -> ⟨ 𝒞 m ⟩
  -- target β (Γ ∙⟮ A ∣ x₁ ⟯) zero refl-≡ = ⟨ Modal (β ◆ restr Γ) ⟩ A
  -- target β (Γ ∙⟮ A ∣ x₁ ⟯) (suc i) p = target β Γ i p
  -- target β (Γ ∙! α) i p = target (β ◆ α) Γ i p


  rule-mod : ∀{Γ : Ctx m n₁} {A : 𝒞Obj {{_}} {{Param}} n₀} -> (μ : n₀ ⟶ n₁)
             -> SemanticHom (Γ ∙! μ) A
             -> SemanticHom Γ (⟨ Modal {{_}} {{Param}} μ ⟩ A)
  rule-mod μ (semanticHom vars goodVars tran term) =
    let xx = true
    in semanticHom vars (λ i j -> goodVars i j ◆ μ) (λ i j -> let ϕ = tran i j in ϕ) {!!}

  rule-letmod : ∀{Γ : Ctx m n₂} {A : 𝒞Obj {{_}} {{Param}} n₀}
                -> {B : 𝒞Obj {{_}} {{Param}} n₂}
                -> (μ : n₀ ⟶ n₁) -> (ν : n₁ ⟶ n₂)
                -> SemanticHom (Γ ∙! ν) (⟨ Modal {{_}} {{Param}} μ ⟩ A)
                -> SemanticHom (Γ ∙⟮ A ∣ μ ◆ ν ⟯) B
                -> SemanticHom Γ B
  rule-letmod {n₂ = n₂} {Γ = Γ} {A} {B} μ ν t s = semanticHom vars' goodVars' {!!} {!!}
    where
      vars' : Fin (length Γ) -> ℕ
      vars' i = vars s (suc i) + vars s zero * vars t i

      goodVars' : (i : Fin (length Γ)) →
                  Fin (vars' i) →
                  (fst (modal∂ Γ i)) ⟶ n₂
      goodVars' i v = caseᶠⁱⁿ v of
                      (λ (j : Fin (vars s (suc i))) -> goodVars s (suc i) j)
                      (λ j -> tupleᶠⁱⁿ j of
                              λ (j₀ : Fin (vars s zero)) (j₁ : Fin (vars t i)) ->
                                    let a0 = goodVars s zero j₀
                                        a1 = goodVars t i j₁
                                    in a1 ◆ ν
                                    )

      tran' : (i : Fin (length Γ)) (j : Fin (vars' i)) → HomOf (𝒞 _) (source Γ i) (target Γ i (goodVars' i j))
      tran' i v = caseᶠⁱⁿ v of
                  ((λ (j : Fin (vars s (suc i))) -> {!!}))
                  {!!}


-}


