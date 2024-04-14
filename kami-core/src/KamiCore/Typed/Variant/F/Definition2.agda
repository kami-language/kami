
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Definition2 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso

-- open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
-- open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition -- hiding (_◆_)
-- open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition

open import Data.Vec hiding ([_] ; map)


record MTTꟳ (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field 𝓂 : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:𝓂}} : isCategory {𝑖 ⌄ 1 ⋯ 2} 𝓂
  field {{is2Category:𝓂}} : is2Category {𝑖 ⌄ 3 ⋯ 4} ′ 𝓂 ′

open MTTꟳ {{...}} public



module Definition-MTTꟳ {𝑖 : 𝔏 ^ 5} {{Param : MTTꟳ 𝑖}} where
  private
    𝓂' : Category _
    𝓂' = ′ 𝓂 ′

  ModeHom : (a b : 𝓂) -> 𝒰 _
  ModeHom a b = a ⟶ b

  private variable
    k l m n o p m₀ n₀ m₁ n₁ l₀ l₁ : 𝓂 {{Param}}
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

  data ⊢Type : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    ⟨_∣_⟩ : ⊢Type m -> m ⟶ n -> ⊢Type n
    Unit : ⊢Type m
    ⟮_∣_⟯⇒_ : ⊢Type m -> m ⟶ n -> ⊢Type n -> ⊢Type n

  infix 30 ⟨_∣_⟩ ⟮_∣_⟯⇒_

  private variable
    A : ⊢Type m
    B : ⊢Type n

  data Ctx : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    ε : Ctx m
    _∙⟮_∣_⟯ : Ctx n -> ⊢Type m -> m ⟶ n -> Ctx n
    _∙!_ : Ctx n -> m ⟶ n -> Ctx m

  infix 32 _∙⟮_∣_⟯
  infixl 30 _∙!_

  data CtxExt : (m ⟶ n) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    ε : CtxExt {m} {m} id
    _∙⟮_∣_⟯ : CtxExt {n} {k} η -> ⊢Type m -> (μ : m ⟶ n) -> CtxExt η
    _∙!_ : CtxExt {n} {k} η -> (ω : m ⟶ n) -> CtxExt (ω ◆ η)

  private variable
    E F G : CtxExt μ

  _⋆_ : Ctx k -> CtxExt {m} {k} η -> Ctx m
  Γ ⋆ ε = Γ
  Γ ⋆ (E ∙⟮ x ∣ μ ⟯) = (Γ ⋆ E) ∙⟮ x ∣ μ ⟯
  Γ ⋆ (E ∙! ω) = (Γ ⋆ E) ∙! ω

  infixl 22 _⋆_

  -- data _⇛_ : (E : CtxExt {m} {n} μ) -> (F : CtxExt {m} {n} ν) -> 𝒰 𝑖 where
  --   id-⇛ : E ⇛ E
  --   _∙‼_ : {μ ν : m ⟶ n} -> E ⇛ F -> (ν ⟹ μ) -> E ∙! μ ⇛ F ∙! ν
  --   _∙⟮_∣_⟯ : E ⇛ F -> (A : ⊢Type k) -> ∀ μ -> E ∙⟮ A ∣ μ ⟯ ⇛ F ∙⟮ A ∣ μ ⟯


  data _⇛_ : (E : CtxExt {m} {n} μ) -> (F : CtxExt {m} {n} ν) -> 𝒰 𝑖 where
    id-⇛ : E ⇛ E
    _∙‼_ : {μ ν : m ⟶ n} -> E ⇛ F -> (ν ⟹ μ) -> E ∙! μ ⇛ F ∙! ν
    comp⁻¹-∙! : {μ₀ : m ⟶ n} {μ₁ : l ⟶ m} -> E ∙! μ₀ ∙! μ₁ ⇛ E ∙! (μ₁ ◆ μ₀)
    comp-∙! : {μ₀ : m ⟶ n} {μ₁ : l ⟶ m} -> E ∙! (μ₁ ◆ μ₀) ⇛ E ∙! μ₀ ∙! μ₁ 
    unit-∙! : {η : m ⟶ n} -> ∀{E : CtxExt η} -> E ⇛ E ∙! id
    unit⁻¹-∙! : {η : m ⟶ n} -> ∀{E : CtxExt η} -> E ∙! id ⇛ E
    _∙⟮_∣_⟯ : E ⇛ F -> (A : ⊢Type k) -> ∀ μ -> E ∙⟮ A ∣ μ ⟯ ⇛ F ∙⟮ A ∣ μ ⟯
    _⨾_ : E ⇛ F -> F ⇛ G -> E ⇛ G


  private variable
    Γ : Ctx m
    Δ : Ctx n
    Ε : Ctx o

  data _⊢Var⟮_∣_⇒_⟯ : (Γ : Ctx k) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) → 𝒰 𝑖 where
    zero : ∀{Γ} {μ : m ⟶ l} -> (Γ ∙⟮ A ∣ μ ⟯) ⊢Var⟮ A ∣ μ ⇒ id ⟯
    suc! : ∀{Γ} {μ : m ⟶ l} {η : k ⟶ l} {ω : o ⟶ k} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙! ω ⊢Var⟮ A ∣ μ ⇒ ω ◆ η ⟯
    suc : Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙⟮ B ∣ ω ⟯ ⊢Var⟮ A ∣ μ ⇒ η ⟯

  delete-me : ∀ {Γ : Ctx k} {A : ⊢Type m} {μ : m ⟶ l} {η : o ⟶ l} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯  -> k ≡ o
  delete-me zero = refl-≡
  delete-me (suc! v) = refl-≡
  delete-me (suc v) = delete-me v

  record _⊢Var⟮_∣_⇒∼_⟯ (Γ : Ctx k) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) : 𝒰 𝑖 where
    constructor varOver
    field target : o ⟶ l
    field fst : Γ ⊢Var⟮ A ∣ μ ⇒ target ⟯
    field snd : η ∼ target

  record _⊢Var⟮_∣_⇒⇒_⟯ (Γ : Ctx k) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) : 𝒰 𝑖 where
    constructor varOver
    field target : o ⟶ l
    field fst : Γ ⊢Var⟮ A ∣ μ ⇒ target ⟯
    field snd : η ⟹ target


  data _⊢_ : Ctx m -> ⊢Type m -> 𝒰 𝑖 where
    var : ∀{μ : _ ⟶ o} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
    tt : Γ ⊢ Unit
    mod : ∀ μ -> Γ ∙! μ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩
    letmod : ∀{μ : m ⟶ n} -> (ν : n ⟶ o)
           -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⟩
           -> Γ ∙⟮ A ∣ μ ◆ ν ⟯ ⊢ B
           -> Γ ⊢ B
    lam : Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
    app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ B -> Γ ⊢ B

  data _⟼_ : Ctx m -> Ctx m -> 𝒰 𝑖 where
    id-Ctx : Γ ⟼ Γ
    _∙‼_ : ∀ Γ -> {μ ν : m ⟶ n} -> μ ⟹ ν -> Γ ∙! ν ⟼ Γ ∙! μ
    _∙!_ : ∀ {Γ Δ : Ctx m} -> Γ ⟼ Δ -> ∀ (μ : n ⟶ m) -> Γ ∙! μ ⟼ Δ ∙! μ
    _∙⟮_⟯ : Γ ⟼ Δ -> Γ ∙! μ ⊢ A -> Γ ⟼ Δ ∙⟮ A ∣ μ ⟯
    lift : Γ ⟼ Δ -> Γ ∙⟮ A ∣ μ ⟯ ⟼ Δ ∙⟮ A ∣ μ ⟯
    -- 𝑝 : Γ ∙⟮ A ∣ μ ⟯ ⟼ Γ
    -- _⨾_ : Γ ⟼ Δ -> Δ ⟼ Ε -> Γ ⟼ Ε

  data _⟼*_ : Ctx m -> Ctx m -> 𝒰 𝑖 where
    [] : Γ ⟼* Γ
    _⨾_ : Γ ⟼* Δ -> Δ ⟼ Ε -> Γ ⟼* Ε

  record Factors (Γ : Ctx m) (Γ' : Ctx n) {η : m ⟶ n} (E : CtxExt η) : 𝒰 𝑖 where
    constructor factors
    field factor-restr : m ⟶ n
    field factor-Ext : CtxExt factor-restr
    field ext : Γ' ⋆ factor-Ext ≡ Γ
    field sub : factor-Ext ⇛ E

  -- refl-Factors : ∀{Γ' : Ctx n} -> {η : m ⟶ n} {E : CtxExt η} -> Factors (Γ' ⋆ E) Γ' E
  -- refl-Factors = factors _ _ refl-≡ id-⇛

  pattern refl-Factors δ = factors _ _ refl-≡ δ



  decide-Var : (μ₁ : l₁ ⟶ k)
             -> {μ₀ : l₁ ⟶ k}
             -> {η : l₀ ⟶ l₁}
             -> {ν₀ : ModeHom m₀ n} {ν₁ : ModeHom l₀ n}
             -> (E : CtxExt {l₀} {l₁} η)
             -- -> (rest : n ⟶ )
             -> {Γ : Ctx _}
             -> ((Γ ∙! μ₀) ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
             -> (((Γ ∙! μ₁) ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯)
                +-𝒰 (∑ λ (ϕ : k ⟶ n) -> Γ ⊢Var⟮ A ∣ ν₀ ⇒ ϕ ⟯ ×-𝒰 η ◆ μ₀ ◆ ϕ ∼ ν₁)
  decide-Var ν  ε (suc! {η = η} v) = right (η , v , unit-l-◆ ◈ refl-∼)
  decide-Var ν (E ∙⟮ x ∣ μ ⟯) zero = left zero
  decide-Var ν (E ∙⟮ x ∣ μ ⟯) (suc v) with decide-Var ν E v
  ... | no v = no (suc v)
  ... | yes v = yes v
  decide-Var μ₁ {μ₀} {η'} {ν₀} {ν₁} (_∙!_ {η = η} E ω) (suc! {η = η₁} {ω = ω} v) with decide-Var μ₁ {μ₀} {η} {ν₀}  E v
  ... | no v = no (suc! v)
  ... | yes (ϕ , t , p) =

    let q0 : ω ◆ η ◆ μ₀ ◆ ϕ ∼ ω ◆ ((η ◆ μ₀) ◆ ϕ)
        q0 = assoc-l-◆ ∙ assoc-l-◆ ∙ (refl-∼ ◈ assoc-r-◆)

        q1 : ω ◆ ((η ◆ μ₀) ◆ ϕ) ∼ ω ◆ η₁
        q1 = refl-∼ ◈ p

        q : ω ◆ η ◆ μ₀ ◆ ϕ ∼ ω ◆ η₁
        q = q0 ∙ q1

    in yes (ϕ , t , q)


  transform-Var : {μ : m ⟶ n} {ν₁ : m ⟶ l} -> Γ ∙! μ ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯ -> (μ ⟹ ν) -> ∑ λ (ν₂ : m ⟶ l) -> Γ ∙! ν ⊢Var⟮ A ∣ ν₀ ⇒ ν₂ ⟯
  transform-Var (suc! t) α = _ , suc! t

  _∙!*-Var_ : {μ : m ⟶ n} -> {η : k ⟶ _} -> Γ ⊢Var⟮ A ∣ μ ⇒ ν ⟯ -> (E : CtxExt η) -> (Γ ⋆ E) ⊢Var⟮ A ∣ μ ⇒∼ η ◆ ν ⟯
  v ∙!*-Var ε = varOver _ v (unit-l-◆)
  v ∙!*-Var (E ∙⟮ x ∣ μ ⟯) = let varOver _ v' p = (v ∙!*-Var E) in varOver _ (suc v') p
  v ∙!*-Var (E ∙! ω) = let varOver _ v' p = (v ∙!*-Var E) in varOver _ (suc! v') (assoc-l-◆ ∙ (refl-∼ ◈ p))

  pushDown-Var : {η₀ : _ ⟶ k} {ν : _ ⟶ _} {E : CtxExt η₀} -> {μ : _ ⟶ n} {η : m₀ ⟶ m₁} {ω : m₀ ⟶ m₁} -> ((Γ ∙! μ) ⋆ E) ⊢Var⟮ A ∣ η ⇒ ω ⟯ -> (μ ⟹ ν) -> (η ⟹ ω) -> ((Γ ∙! ν) ⋆ E) ⊢ A
  pushDown-Var {η₀ = η₀} {ν} {E = E} {μ} {η} {ω} v α β with decide-Var ν E v
  ... | no x = var x β
  ... | yes (ϕ , v' , p) =
    let α0 : η ⟹ ω
        α0 = β

        α1 : ω ⟹ (η₀ ◆ μ) ◆ ϕ
        α1 = ⟨ 2celliso p ⟩⁻¹

        α2 : (η₀ ◆ μ) ◆ ϕ ⟹ η₀ ◆ (μ ◆ ϕ)
        α2 = α-l-◆

        α3 : η₀ ◆ (μ ◆ ϕ) ⟹ η₀ ◆ (ν ◆ ϕ)
        α3 = id {{2HomData}} ⇃◆⇂ (α ⇃◆⇂ id {{2HomData}})

        varOver ρ v q = (suc! v') ∙!*-Var E

        α4 : η₀ ◆ (ν ◆ ϕ) ⟹ ρ
        α4 = ⟨ 2celliso q ⟩

    in var (v) (α0 ◆ α1 ◆ α2 ◆ α3 ◆ α4)

  pushDown : ∀ Γ (E : CtxExt η) -> {μ : _ ⟶ n} -> ((Γ ∙! μ) ⋆ E) ⊢ A -> (μ ⟹ ν) -> ((Γ ∙! ν) ⋆ E) ⊢ A
  pushDown Γ E (var x β) α = pushDown-Var x α β
  pushDown Γ E tt α = tt
  pushDown Γ E (mod μ t) α = mod μ (pushDown Γ (E ∙! μ) t α)
  pushDown Γ E (letmod ν t s) α = letmod ν (pushDown Γ (E ∙! ν) t α) (pushDown Γ (E ∙⟮ _ ∣ _ ⟯) s α)
  pushDown Γ E (lam t) α = lam (pushDown _ _ t α)
  pushDown Γ E (app t s) α = app (pushDown Γ E t α) (pushDown Γ (E ∙! _) s α)

  wk-Var : ∀ (E : CtxExt η) -> (Γ ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯ -> (Γ ∙⟮ B ∣ μ ⟯ ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
  wk-Var ε v = suc v
  wk-Var (E ∙⟮ x ∣ μ ⟯) zero = zero
  wk-Var (E ∙⟮ x ∣ μ ⟯) (suc v) = suc (wk-Var E v)
  wk-Var (E ∙! ω) (suc! v) = suc! (wk-Var E v)

  wk : ∀ (E : CtxExt η) -> (Γ ⋆ E) ⊢ A -> (Γ ∙⟮ B ∣ μ ⟯ ⋆ E) ⊢ A
  wk E (var x α) = var (wk-Var E x) α
  wk E tt = tt
  wk E (mod μ t) = mod μ (wk (E ∙! μ) t)
  wk E (letmod ν t s) = letmod ν (wk (E ∙! ν) t) (wk (E ∙⟮ _ ∣ _ ⟯) s)
  wk E (lam t) = lam (wk (E ∙⟮ _ ∣ _ ⟯) t)
  wk E (app t s) = app (wk E t) (wk (E ∙! _) s)

  map-Var : {E₀ : CtxExt η₀} {E₁ : CtxExt η₁} -> E₁ ⇛ E₀
                    -> (Γ ⋆ E₀) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
                    -> (Γ ⋆ E₁) ⊢Var⟮ A ∣ ν₀ ⇒⇒ ν₁ ⟯
  map-Var id-⇛ t = varOver _ t id
  map-Var (ξ ∙‼ α) (suc! t) = let varOver _ v' β = map-Var ξ t in varOver _ (suc! v') (α ⇃◆⇂ β)
  map-Var comp⁻¹-∙! (suc! t) = varOver _ (suc! (suc! t)) α-l-◆
  map-Var comp-∙! (suc! (suc! t)) = varOver _ (suc! t) α-r-◆
  map-Var unit-∙! (suc! t) = varOver _ t υ-l-◆
  map-Var unit⁻¹-∙! t
    with refl-≡ <- delete-me t
    = varOver _ (suc! t) υ⁻¹-l-◆
  map-Var (ξ ∙⟮ A ∣ μ ⟯) zero = varOver _ zero id
  map-Var (ξ ∙⟮ A ∣ μ ⟯) (suc t) = let varOver _ v' β = map-Var ξ t in varOver _ (suc v') β
  map-Var (ξ ⨾ ξ₁) t =
    let varOver _ v' β = map-Var ξ₁ t
        varOver _ v'' β' = map-Var ξ v'
    in varOver _ v'' (β ◆ β')

  map-Var-cong : {E₀ : CtxExt η₀} {E₁ : CtxExt η₁} -> E₁ ⇛ E₀ -> (F : CtxExt ω)
                    -> (Γ ⋆ E₀ ⋆ F) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
                    -> (Γ ⋆ E₁ ⋆ F) ⊢Var⟮ A ∣ ν₀ ⇒⇒ ν₁ ⟯
  map-Var-cong ξ ε v = map-Var ξ v
  map-Var-cong ξ (F ∙⟮ x ∣ μ ⟯) zero = varOver _ zero id
  map-Var-cong ξ (F ∙⟮ x ∣ μ ⟯) (suc v) = let varOver _ v' p = map-Var-cong ξ F v in varOver _ (suc v') p
  map-Var-cong ξ (F ∙! ω) (suc! v) = let varOver _ v' p = map-Var-cong ξ F v in varOver _ (suc! v') (id ⇃◆⇂ p)

  map-cong : {E₀ : CtxExt η₀} {E₁ : CtxExt η₁} -> E₁ ⇛ E₀ -> (F : CtxExt ω)
                    -> (Γ ⋆ E₀ ⋆ F) ⊢ A
                    -> (Γ ⋆ E₁ ⋆ F) ⊢ A
  map-cong ξ F (var x α) = let varOver _ v p = map-Var-cong ξ F x in var v (α ◆ p )
  map-cong ξ F tt = tt
  map-cong ξ F (mod μ t) = mod μ (map-cong ξ (F ∙! μ) t)
  map-cong ξ F (letmod ν t s) = letmod ν (map-cong ξ (F ∙! ν) t) (map-cong ξ (F ∙⟮ _ ∣ _ ⟯) s)
  map-cong ξ F (lam t) = lam (map-cong ξ (F ∙⟮ _ ∣ _ ⟯) t)
  map-cong ξ F (app t s) = app (map-cong ξ F t) (map-cong ξ (F ∙! _) s)

  map-comp-∙! : ∀{μ : n ⟶ o} {ω : m ⟶ n} -> Γ ∙! μ ∙! ω ⊢ A -> Γ ∙! (ω ◆ μ) ⊢ A
  map-comp-∙! {Γ = Γ} = map-cong {Γ = Γ} comp-∙! ε

  map-comp⁻¹-∙! : ∀{μ : n ⟶ o} {ω : m ⟶ n} -> Γ ∙! (ω ◆ μ) ⊢ A -> Γ ∙! μ ∙! ω ⊢ A
  map-comp⁻¹-∙! {Γ = Γ} = map-cong {Γ = Γ} comp⁻¹-∙! ε

  map-unit-∙! : ∀{Γ : Ctx k} -> Γ ∙! id ⊢ A -> Γ ⊢ A
  map-unit-∙! {Γ = Γ} = map-cong {Γ = Γ} unit-∙! ε

  map-unit⁻¹-∙! :  ∀{Γ : Ctx k} -> Γ ⊢ A -> Γ ∙! id ⊢ A
  map-unit⁻¹-∙! {Γ = Γ} = map-cong {Γ = Γ} unit⁻¹-∙! ε

  wk!-ind : ∀(E : CtxExt η) -> ∀ μ -> (Γ ∙! η) ∙! μ ⊢ A -> (Γ ⋆ E) ∙! μ ⊢ A
  wk!-ind {Γ = Γ} ε μ t = map-cong {Γ = Γ} ((id-⇛ ∙‼ υ-r-◆) ⨾ comp-∙!) ε t 
  wk!-ind (E ∙⟮ x ∣ ν ⟯) μ t = let X = wk!-ind E μ t in wk (ε ∙! μ) X
  wk!-ind {Γ = Γ} (E ∙! ω) μ t =
    let res : Γ ⋆ E ∙! (μ ◆ ω) ⊢ _
        res = (wk!-ind E (μ ◆ ω) (map-cong {Γ = Γ} ((comp⁻¹-∙! ⨾ (id-⇛ ∙‼ α-r-◆)) ⨾ comp-∙!) ε t))
    in map-cong {Γ = Γ ⋆ E} {E₀ = (ε ∙! (μ ◆ ω))} {E₁ = (ε ∙! ω ∙! μ)} comp⁻¹-∙! ε res

  wk! : ∀(E : CtxExt η) -> (Γ ∙! η) ⊢ A -> (Γ ⋆ E) ⊢ A
  wk! E t = map-unit-∙! (wk!-ind E id (map-unit⁻¹-∙! t))




  Skip : ∀ Γ Δ -> Γ ⟼ Δ -> {η : k ⟶ l} -> Δ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> ∑ λ Γ' -> ∑ λ (E : CtxExt η) -> (Γ' ∙! μ ⊢ A) × Factors Γ Γ' E
  Skip (Γ ∙⟮ A ∣ μ ⟯) .(_ ∙⟮ _ ∣ _ ⟯) id-Ctx zero = Γ ∙⟮ A ∣ μ ⟯ , ε , var (suc! zero) υ⁻¹-r-◆ , refl-Factors id-⇛
  Skip (Γ ∙! μ) .(_ ∙! _) id-Ctx (suc! v) with
    (Γ' , E , t , refl-Factors γ) <- Skip Γ _ id-Ctx v
    = Γ' , (E ∙! μ) , t , refl-Factors (γ ∙‼ id {{2HomData}})
  Skip (Γ ∙⟮ _ ∣ _ ⟯) .(_ ∙⟮ _ ∣ _ ⟯) id-Ctx (suc v)
    with (Γ' , E , t , refl-Factors γ) <- Skip Γ _ id-Ctx v
    = Γ' , E ∙⟮ _ ∣ _ ⟯ , t , refl-Factors ((γ ∙⟮ _ ∣ _ ⟯))
  Skip (Γ ∙! _) (Γ ∙! μ) (Γ ∙‼ α) (suc! v) with
    (Γ' , E , t , refl-Factors γ) <- Skip Γ _ id-Ctx v
    = Γ' , (E ∙! μ) , t , refl-Factors (γ ∙‼ α)
  Skip .(_ ∙! _) .(_ ∙! _) (δ ∙! μ) (suc! v) with
    (Γ' , E , t , refl-Factors γ) <- Skip _ _ δ v
    = Γ' , (E ∙! _) , t , refl-Factors (γ ∙‼ id {{2HomData}})
  Skip Γ .(_ ∙⟮ _ ∣ _ ⟯) (δ ∙⟮ x ⟯) zero = Γ , ε , x , refl-Factors id-⇛
  Skip Γ .(_ ∙⟮ _ ∣ _ ⟯) (δ ∙⟮ x ⟯) (suc v)
    with (Γ' , E , t , refl-Factors γ) <- Skip _ _ δ v
    = Γ' , E , t , refl-Factors γ
  Skip (Γ ∙⟮ A ∣ μ ⟯) (Δ ∙⟮ .A ∣ .μ ⟯) (lift δ) zero = (Γ ∙⟮ A ∣ μ ⟯) , ε , var (suc! zero) υ⁻¹-r-◆ , refl-Factors id-⇛ 
  Skip (Γ ∙⟮ A ∣ μ ⟯) (Δ ∙⟮ .A ∣ .μ ⟯) (lift δ) (suc x)
    with Γ' , E , t , refl-Factors ξ <- Skip Γ Δ δ x
    = Γ' , E ∙⟮ A ∣ μ ⟯ , t , refl-Factors (ξ ∙⟮ A ∣ μ ⟯)


  _[_] : Δ ⊢ A -> (δ : Γ ⟼ Δ) -> Γ ⊢ A
  var x α [ δ ]
    with Γ' , E , t , refl-Factors ξ <- Skip _ _ δ x
    with t' <- pushDown _ ε t α
    with t'' <- wk! E t'
    with t''' <- map-cong ξ ε t''
    = t'''
  tt [ δ ] = tt
  mod μ t [ δ ] = mod μ (t [ δ ∙! μ ])
  letmod ν t s [ δ ] = letmod ν (t [ δ ∙! ν ]) (s [ lift δ ])
  lam t [ δ ] = lam (t [ lift δ ])
  app t s [ δ ] = app (t [ δ  ]) (s [ δ ∙! _ ])


{-
-}






{-
{-

open import Agora.TypeTheory.Notation

-- instance
--   isTypeTheory:MTTꟳ : isTypeTheory (MTTꟳ 𝑖)
--   isTypeTheory:MTTꟳ = record
--     { Ctx = Definition-MTTꟳ.Ctx
--     ; ⊢Type = Definition-MTTꟳ.⊢Type
--     ; _⊢_ = λ {{a}} -> λ {m : 𝓂} -> Definition-MTTꟳ._⊢_ {m = m}
--     }





-- module _ {{mtt : MTTꟳ 𝑖}} {a b : ℕ} where
--   testss : {m : 𝓂} -> (Γ : [ mtt ]-Ctx m) -> ∀{A : ⊢Type m} -> Γ ⊢ A
--   testss = {!!}



{-
-}

{-


record MotiveMTT (M : ModeSystem 𝑖) (𝑗 : 𝔏 ^ 3) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field ⟦_⟧-Mode : 0Cell (graph M) -> Category 𝑗
  field ⟦_⟧-Modality : ∀{a b} -> 1Cell (graph M) a b -> Functor ⟦ a ⟧-Mode ⟦ b ⟧-Mode
  field ⟦_⟧-Transformation : ∀{a b} -> (μ ν : 1Cell (graph M) a b)
                             -> ∀{v} -> (ξ : 2Cell (graph M) v μ ν)
                             -> Natural ⟦ μ ⟧-Modality ⟦ ν ⟧-Modality


---------------------------------------------
-- A translation target for ChorMTT

open import Agora.Setoid.Morphism
open import Agora.Setoid.Definition
open import Agora.Category.Std.Category.Definition
-- open import Agora.Category.Std.Category.Instance.Category
open import Agora.Category.Std.Category.Instance.2Category
open import Agora.Category.Std.Category.Instance.CategoryLike
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition

open import Agora.Category.Std.Limit.Specific.Product.Definition
open import Agora.Category.Std.Limit.Specific.Product.Instance.Functor
open import Agora.Category.Std.Category.Structured.FiniteProduct.Definition
open import Agora.Category.Std.Functor.Adjoint.Definition
open import Agora.Category.Std.Functor.Constant
open import Agora.Category.Std.Category.Construction.Product
open import Agora.Category.Std.Closure.Exponential.Definition

open import Data.Fin using (Fin ; suc ; zero)
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Order.StrictOrder.Base

instance
  hasDecidableEquality:Fin : ∀{n} -> hasDecidableEquality (Fin n)
  hasDecidableEquality:Fin = hasDecidableEquality:byStrictOrder

module _ {𝓂 : 𝒰 _} {{_ : CartesianClosedCategory 𝑖 on 𝓂}} where


  private variable n : ℕ

  State : ℕ -> 𝒰 _
  State n = Fin n -> 𝓂

  empty : State n
  empty = const ⊤

  at : (i : Fin n) -> State n -> State n
  at i X j with i ≟ j
  ... | yes _ = X i
  ... | no _ = ⊤


  module _ {n : ℕ} where

    private variable
      i : Fin n

    record Local (i : Fin n) : 𝒰 𝑖 where
      constructor local
      field states : Fin n -> 𝓂

    open Local public

    macro 𝔩 = #structureOn Local

    record Hom-𝔩 (v w : 𝔩 i) : 𝒰 𝑖 where
      field ⟨_⟩ : states v i ⟶ states w i

    record Global : 𝒰 𝑖 where
      constructor global
      field states : Fin n -> 𝓂

    open Global public

    macro 𝔤 = #structureOn Global

    record Hom-𝔤 (v w : 𝔤) : 𝒰 𝑖 where
      field ⟨_⟩ : ∀{i} -> (states v) i ⟶ (states w) i

    -----------------------------------------
    -- the functors
    ＠⁻¹ : 𝔤 -> 𝔩 i
    ＠⁻¹ (global X) = local X

    □⁻¹ : 𝔩 i -> 𝔤
    □⁻¹ (local X) = global X

    ＠ᵘ : 𝔩 i -> 𝔤
    ＠ᵘ {i = i} (local X) = global (at i X)

-}















  -- record 𝔤 : 𝒰 𝑖 where
  --   field 

-- mutual
--   GlobalType : (n : ℕ) -> 𝒰₀
--   GlobalType n = Vec (LocalType n) n

--   -- data GlobalType (n : ℕ) : 𝒰₀ where
--   --   Par : Vec (LocalType n) n -> GlobalType n
--   --   _⇒_ : GlobalType n -> GlobalType n -> GlobalType n

--   data LocalType (n : ℕ) : 𝒰₀ where
--     NN : LocalType n
--     One : LocalType n
--     _⇒_ : LocalType n -> LocalType n -> LocalType n
--     _××_ : LocalType n -> LocalType n -> LocalType n
--     Box : GlobalType n -> LocalType n


{-
open import KamiTheory.Main.Dependent.Untyped.Definition using (Con ; ε ; _∙_)



open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Example
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition

open import Data.Fin using (#_ ; zero ; suc ; Fin)
open import Data.List using (_∷_ ; [])
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

-- open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition

open import KamiTheory.Basics hiding (typed)
open import KamiTheory.Order.Preorder.Instances

module _ (n : ℕ) where

  PP : Preorder _
  PP = ′ StdVec 𝟚 n ′

  postulate instance
    _ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)

  M : ModeSystem _
  M = SendReceiveNarrow-ModeSystem.SRN-ModeSystem PP {{it}} {{it}}


  One-○ : GlobalType n
  One-○ = (iterate (λ x -> x) One n)

  _××-○_ : GlobalType n -> GlobalType n -> GlobalType n
  _××-○_ X Y = zipWith _××_ X Y

  _⇒-○_ : GlobalType n -> GlobalType n -> GlobalType n
  _⇒-○_ X Y = zipWith _⇒_ X Y

  mutual
    data _⊢○_ {k} : Con (λ _ -> GlobalType n) k -> GlobalType n -> 𝒰₀ where
      tt : ∀{Γ} -> Γ ⊢○ One-○
      lam : ∀{Γ A B} -> Γ ∙ A ⊢○ B -> Γ ⊢○ (A ⇒-○ B)
      app : ∀{Γ A B} -> Γ ⊢○ (A ⇒-○ B) -> Γ ⊢○ A -> Γ ⊢○ B


  UnAt-Type : (i : Fin n) -> GlobalType n -> LocalType n
  UnAt-Type i X = lookup X i
  ⟦＠⁻¹_⟧ = UnAt-Type

  UnBox-Type : LocalType n -> GlobalType n

  ⟦□⁻¹⟧ = UnBox-Type

  UnBox-Type (Box X) = X
  UnBox-Type NN = One-○
  UnBox-Type One = One-○
  UnBox-Type (X ⇒ Y) = ⟦□⁻¹⟧ X ⇒-○ UnBox-Type Y
  UnBox-Type (X ×× Y) = UnBox-Type X ××-○ UnBox-Type Y


{-
  target : MotiveMTT M {!!}
  target = {!!}
  -}
-}
-}
-}
