
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model3 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_)
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
open import Agora.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Category.Instance.CategoryLike
open import Agora.Category.Std.Functor.Instance.Category
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Closure.Exponential.Definition
open import Agora.Category.Std.Functor.Adjoint.Definition
open import Agora.Data.Fin.Definition

open import Agora.Data.FinSet.Definition
open import Agora.Data.FinSet.Instance.Category
open import Agora.Data.FinSet.Instance.FiniteCoproductCategory
open import Agora.Data.FinSet.Instance.FiniteProductCategory

open import Data.Vec hiding ([_] ; map ; length)
open import Data.Fin using (Fin ; suc ; zero)
open import Data.Nat using (_+_ ; _*_)



record MTTꟳ (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field 𝓂 : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:𝓂}} : isCategory {𝑖 ⌄ 1 ⋯ 2} 𝓂
  field {{is2Category:𝓂}} : is2Category {𝑖 ⌄ 3 ⋯ 4} ′ 𝓂 ′

open MTTꟳ {{...}} public

record Model-MTTꟳ 𝑗 {{A : MTTꟳ 𝑖}} : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field 𝕄 : 𝓂 -> Category 𝑗
  𝕄Obj : 𝓂 -> 𝒰 _
  𝕄Obj m = ⟨ 𝕄 m ⟩

  -- field 𝒟 : CartesianClosedCategory 𝑗
  -- field {{isCartesianClosedCategory:𝒟}} : isCartesianClosedCategory 𝒟
  field {{hasFiniteProducts:𝕄}} : ∀ {m} -> hasFiniteProducts (𝕄 m)
  -- field embed : ∀ m -> Functor (𝕄 m) (↳ (↳ 𝒟))
  field Modal : ∀{a b : 𝓂} -> a ⟶ b -> Functor (𝕄 a) (𝕄 b)
  field functoriality-◆-Modal : ∀{m n o : 𝓂} -> ∀{α : m ⟶ n} {β : n ⟶ o} -> Modal (α ◆ β) ∼ Modal α ◆-𝐂𝐚𝐭 Modal β
  field isSetoidHom:map-Modal : ∀{m n : 𝓂} -> ∀{α β : m ⟶ n} -> α ∼ β -> Modal α ∼ Modal β
  field transform : ∀{ a b : 𝓂} -> (μ ν : a ⟶ b) -> μ ⟹ ν -> Modal μ ⟶ Modal ν


  field {{hasExponentials:𝕄}} : ∀{m} -> hasExponentials (′ ⟨ 𝕄 m ⟩ ′)

  private instance
    isCategory:𝕄 : ∀{m} -> isCategory ⟨ (𝕄 m) ⟩
    isCategory:𝕄 = of (𝕄 _)

  field preserve-Exp : ∀{a b : 𝓂} -> (μ : a ⟶ b) -> ∀{X Y} -> ⟨ Modal μ ⟩ [ X , Y ] ≅ [ ⟨ Modal μ ⟩ X , ⟨ Modal μ ⟩ Y ]



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

  instance
    isCategory:𝕄 : isCategory ⟨ (𝕄 m) ⟩
    isCategory:𝕄 = of (𝕄 _)

  instance
    isCategoryData:𝕄 : isCategoryData (⟨ 𝕄 m ⟩) _
    isCategoryData:𝕄 = HomData

  instance
    hasFiniteProducts':𝕄 : hasFiniteProducts (𝕄 m)
    hasFiniteProducts':𝕄 = hasFiniteProducts:𝕄

  instance
    hasTerminal:𝕄 : hasTerminal (𝕄 m)
    hasTerminal:𝕄 = hasTerminal:this

  instance
    hasProducts:𝕄 : hasProducts (𝕄 m)
    hasProducts:𝕄 = hasProducts:this

  instance
    isProduct:⊓-𝕄 : ∀{a b : ⟨ 𝕄 m ⟩} -> isProduct a b (a ⊓ b)
    isProduct:⊓-𝕄 = isProduct:⊓

  -- instance
  --   hasExponentials:𝕄 : hasExponentials (′ ⟨ 𝕄 m ⟩ ′)
  --   hasExponentials:𝕄 = {!!}

  -- instance
  --   isExponential:𝕄 : ∀{X : ⟨ 𝕄 m ⟩} -> isExponential (obj X)
  --   isExponential:𝕄 = {!!}

  data Ctx : (m n : 𝓂) -> 𝒰 (𝑖 ､ 𝑗) where
    ε : Ctx m m
    _∙⟮_∣_⟯ : Ctx k n -> ⟨ 𝕄 m ⟩ -> m ⟶ n -> Ctx k n
    _∙!_ : Ctx k n -> m ⟶ n -> Ctx k m

  infix 32 _∙⟮_∣_⟯
  infixl 30 _∙!_


  private variable
    Γ : Ctx m n

  data ⟮_∣_⇒_⟯∈_ {m l} (A : ⟨ 𝕄 m ⟩) (μ : m ⟶ l) : (η : k ⟶ l) (Γ : Ctx o k) → 𝒰 (𝑖 ､ 𝑗) where
    zero : ∀{Γ : Ctx o l} -> ⟮ A ∣ μ ⇒ idOn l ⟯∈ (Γ ∙⟮ A ∣ μ ⟯)
    suc! : ∀{Γ : Ctx o k} {η : k ⟶ l} {ω : p ⟶ k} -> ⟮ A ∣ μ ⇒ η ⟯∈ Γ -> ⟮ A ∣ μ ⇒ ω ◆ η ⟯∈ Γ ∙! ω
    suc : ∀{B} -> ⟮ A ∣ μ ⇒ η ⟯∈ Γ -> ⟮ A ∣ μ ⇒ η ⟯∈ Γ ∙⟮ B ∣ ω ⟯

  record Varᵘ (Γ : Ctx o k) : 𝒰 (𝑖 ､ 𝑗) where
    field origin : 𝓂
    field current : 𝓂
    field source : origin ⟶ current
    field target : k ⟶ current
    field type : ⟨ 𝕄 origin ⟩
    field ix : ⟮ type ∣ source ⇒ target ⟯∈ Γ

  -- record Varᵘ (Γ : Ctx o k) : 𝒰 (𝑖 ､ 𝑗) where
  --   field origin : 𝓂
  --   field current : 𝓂
  --   field source : origin ⟶ current
  --   field target : origin ⟶ current
  --   field type : ⟨ 𝕄 origin ⟩
  --   field ix : ⟮ type ∣ source ⇒ target ⟯∈ Γ

  open Varᵘ public

  instance
    isFinite:Var : isFinite (Varᵘ Γ)
    isFinite:Var = record { size = {!!} ; index = {!!} ; isIso:index = {!!} }

  module _ (Γ : Ctx o k) where
    macro Var = #structureOn (Varᵘ Γ)

  suc!-Var : Var Γ -> Var (Γ ∙! μ)
  suc!-Var v = record { ix = suc! (ix v)}

  suc-Var : Var Γ -> ∀{A} -> Var (Γ ∙⟮ A ∣ μ ⟯)
  suc-Var v = record { ix = suc (ix v)}

  zero-Var : ∀{A} -> Var (Γ ∙⟮ A ∣ μ ⟯)
  zero-Var = record {ix = zero}





  restr : (Γ : Ctx m n) -> n ⟶ m
  restr ε = id
  restr (Γ ∙⟮ A ∣ α ⟯) = restr Γ
  restr (Γ ∙! α) = α ◆ restr Γ

{-

  partrestr : (Γ : Ctx m o) -> {μ : l ⟶ k} {η : o ⟶ k} -> ∀{A : ⟨ 𝕄 l ⟩} ->  (v : ⟮ A ∣ μ ⇒ η ⟯∈ Γ) -> o ⟶ k
  partrestr (Γ ∙⟮ x ∣ x₁ ⟯) zero = id
  partrestr (Γ ∙⟮ x ∣ x₁ ⟯) (suc v) = partrestr Γ v
  partrestr (Γ ∙! x) (suc! v) = let X = partrestr Γ v in x ◆ X


  length : Ctx m n -> ℕ
  length ε = 0
  length (Γ ∙⟮ x ∣ x₁ ⟯) = suc (length Γ)
  length (Γ ∙! x) = length Γ

  modal∂ : (Γ : Ctx m n) -> (i : Fin (length Γ)) -> 𝓂 × 𝓂
  modal∂ {n = n} (_∙⟮_∣_⟯ {m = m} Γ x α) zero = m , n
  modal∂ (Γ ∙⟮ x ∣ x₁ ⟯) (suc i) = modal∂ Γ i
  modal∂ (Γ ∙! x) i = modal∂ Γ i

  thm01 : ∀ (Γ : Ctx m n) i -> snd (modal∂ Γ i) ≡ n
  thm01 (Γ ∙⟮ x ∣ x₁ ⟯) zero = {!!}
  thm01 (Γ ∙⟮ x ∣ x₁ ⟯) (suc i) = {!!}
  thm01 (Γ ∙! x) i = {!!}



  cut-Ind : (Γ : Ctx m o) -> {μ : l ⟶ k} {η : o ⟶ k} -> ∀{A : ⟨ 𝕄 l ⟩} ->  (v : ⟮ A ∣ μ ⇒ η ⟯∈ Γ) -> Ctx m k
  cut-Ind (Γ ∙⟮ _ ∣ _ ⟯) zero = Γ
  cut-Ind (Γ ∙! _) (suc! v) = cut-Ind Γ v
  cut-Ind (Γ ∙⟮ _ ∣ _ ⟯) (suc v) = cut-Ind Γ v

  cut : (Γ : Ctx m n) -> (v : Var Γ) -> Ctx m (current v)
  cut Γ v = {!!}


  -- lo : (Γ : Ctx m n) -> Var Γ -> ⟨ 𝕄 m ⟩
  -- lo Γ v = {!!}

  source' : (Γ : Ctx m n) -> (v : Var Γ) -> ⟨ 𝕄 m ⟩
  source' Γ v = ⟨ Modal (source v ◆ restr (cut Γ v)) ⟩ (type v)

  -- target' : (Γ : Ctx m n) -> (v : Var Γ) -> fst (modal∂ Γ i) ⟶ n -> ⟨ 𝕄 m ⟩
  -- target' : (Γ : Ctx m n) -> (v : Var Γ) -> current v ⟶ n -> ⟨ 𝕄 m ⟩
  -- target' Γ v α = let β = partrestr Γ (ix v) in let A = type v in let γ = restr (cut Γ v) in ⟨ Modal (β ◆ γ) ⟩ A

  target' : (Γ : Ctx m n) -> (v : Var Γ) -> origin v ⟶ n -> ⟨ 𝕄 m ⟩
  target' Γ v α =
    let β = partrestr Γ (ix v)
        γ = restr (cut Γ v)
    in ⟨ Modal (α ◆ β ◆ γ) ⟩ (type v)


-}

  ------------------------------------------------------------------------
  -- Notation
  𝕄[_] : ∀(μ : m ⟶ n) -> ⟨ 𝕄 m ⟩ -> ⟨ 𝕄 n ⟩
  𝕄[_] μ = ⟨ Modal μ ⟩

  functoriality-◆-𝕄 : ∀{α : m ⟶ n} {β : n ⟶ o} -> ∀{A} -> 𝕄[ α ◆ β ] A ⟶ 𝕄[ β ] (𝕄[ α ] A)
  functoriality-◆-𝕄 {α = α} {β = β} {A = A} =
    let N = functoriality-◆-Modal {α = α} {β = β}
        N' = ⟨ ⟨ N ⟩ ⟩ A
    in N'

  functoriality⁻¹-◆-𝕄 : ∀{α : m ⟶ n} {β : n ⟶ o} -> ∀{A} -> 𝕄[ β ] (𝕄[ α ] A) ⟶ 𝕄[ α ◆ β ] A
  functoriality⁻¹-◆-𝕄 {α = α} {β = β} {A = A} =
    let N = functoriality-◆-Modal {α = α} {β = β}
        N' = ⟨ ⟨ N ⟩⁻¹ ⟩ A
    in N'

  cong-𝕄 : ∀{α β : m ⟶ n} -> α ∼ β -> ∀{A} -> 𝕄[ α ] A ⟶ 𝕄[ β ] A
  cong-𝕄 p {A} =
    let p' = isSetoidHom:map-Modal p
        p'' = ⟨ ⟨ p' ⟩ ⟩ A
    in p''

  ------------------------------------------------------------------------

  ⟦_⟧-Ctx : Ctx m n -> ⟨ 𝕄 m ⟩
  ⟦ ε ⟧-Ctx = ⊤
  ⟦ Γ ∙⟮ x ∣ μ ⟯ ⟧-Ctx = ⟦ Γ ⟧-Ctx ⊓ (⟨ Modal (μ ◆ restr Γ) ⟩ x)
  ⟦ Γ ∙! x ⟧-Ctx = ⟦ Γ ⟧-Ctx

  SemanticHom : (Γ : Ctx m n) (A : 𝕄Obj n) -> 𝒰 _
  SemanticHom {m = m} Γ A = ⟦ Γ ⟧-Ctx ⟶ ⟨ Modal (restr Γ) ⟩ A


  rule-var : {Γ : Ctx m n₁} {A : 𝕄Obj {{_}} {{Param}} n₀} {μ : n₀ ⟶ k} -> ⟮ A ∣ μ ⇒ ν ⟯∈ Γ
             -> ∀ η -> (α : μ ⟹ (η ◆ ν)) -> SemanticHom Γ (𝕄[ η ] A)
  rule-var zero μ α = π₁ ◆ (functoriality-◆-𝕄 ◆ mapOf (Modal _) (⟨ transform _ _ (α ◆ υ-r-◆) ⟩ _))
  rule-var (suc! {ω = ω} i) μ α = let x = rule-var i (μ ◆ ω) {!!} in {!!}
  rule-var (suc i) μ α = {!!}

  rule-lam : {Γ : Ctx k n} -> {μ : m ⟶ n} -> ∀{A B}
             -> SemanticHom (Γ ∙⟮ A ∣ μ ⟯) B
             -> SemanticHom Γ [ (𝕄[ μ ] A) , B ]
  rule-lam {Γ = Γ} {μ = μ} t =
    let t' = curry t
    in t' ◆ ([map functoriality⁻¹-◆-𝕄 , _ ] ◆ ⟨ preserve-Exp (restr Γ) ⟩⁻¹ )

  rule-app : {Γ : Ctx k n} -> {μ : m ⟶ n} -> ∀{A B}
             -> SemanticHom Γ [ (𝕄[ μ ] A) , B ]
             -> SemanticHom (Γ ∙! μ) A
             -> SemanticHom Γ B
  rule-app t s =
    let t' = uncurry (t ◆ ⟨ preserve-Exp _ ⟩)
    in ⧼ id , s ◆ functoriality-◆-𝕄 ⧽ ◆ t'


  rule-mod : ∀{Γ : Ctx m n₁} {A : 𝕄Obj {{_}} {{Param}} n₀} -> (μ : n₀ ⟶ n₁)
             -> SemanticHom (Γ ∙! μ) A
             -> SemanticHom Γ (⟨ Modal {{_}} {{Param}} μ ⟩ A)
  rule-mod {Γ = Γ} {A = A} μ t = t ◆ functoriality-◆-𝕄


  rule-letmod : ∀{Γ : Ctx m n₂} {A : 𝕄Obj {{_}} {{Param}} n₀}
                -> {B : 𝕄Obj {{_}} {{Param}} n₂}
                -> (μ : n₀ ⟶ n₁) -> (ν : n₁ ⟶ n₂)
                -> SemanticHom (Γ ∙! ν) (⟨ Modal {{_}} {{Param}} μ ⟩ A)
                -> SemanticHom (Γ ∙⟮ A ∣ μ ◆ ν ⟯) B
                -> SemanticHom Γ B
  rule-letmod μ ν t s = ⧼ id , t ◆ (functoriality⁻¹-◆-𝕄 ◆ cong-𝕄 assoc-r-◆) ⧽ ◆ s

{-
-}


