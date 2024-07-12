
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.MTT.Definition where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Data.Product.Definition
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition
open import Agora.Category.Std.Morphism.Iso
open import Agora.Category.Std.Category.Structured.Classified.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import Data.Vec hiding ([_] ; map)


record MTT (𝑖 : 𝔏 ^ 6) : 𝒰 (𝑖 ⁺) where
  field ModeTheory : 2Category (𝑖 ⌄ 0 ⋯ 4)
  field isTargetMode : ⟨ ModeTheory ⟩ -> 𝒰 (𝑖 ⌄ 5)
  field Classification : JoinSemilattice (ℓ₀ , ℓ₀ , ℓ₀)
  field {{isClassified:Transformation}} : ∀{a b : ⟨ ModeTheory ⟩} -> isClassified Classification (HomCategory a b)
  field pureTrans : ⟨ Classification ⟩
  field impureTrans : ⟨ Classification ⟩


open MTT public



module 𝔐TT/Definition {𝑖 : 𝔏 ^ 6} (This : MTT 𝑖) where
  private
    𝓂' : Category _
    𝓂' = ↳ (This .ModeTheory)

    𝓂 = ⟨ This .ModeTheory ⟩

    ModeHom : (a b : 𝓂) -> 𝒰 _
    ModeHom a b = a ⟶ b

  module Variables/Mode where variable
    k l m n o p m₀ n₀ m₁ n₁ l₀ l₁ : ⟨ This .ModeTheory ⟩

  open Variables/Mode

  module Variables/Hom where variable
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

  open Variables/Hom

  module [𝔐TT/Definition::Type] where
    data ⊢Type : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
      ⟨_∣_⟩ : ⊢Type m -> m ⟶ n -> ⊢Type n
      Unit : ⊢Type m
      Tr : ⊢Type m -> ⊢Type m
      Either : ⊢Type m -> ⊢Type m -> ⊢Type m
      Lst : ⊢Type m -> ⊢Type m
      ⟮_∣_⟯⇒_ : ⊢Type m -> m ⟶ n -> ⊢Type n -> ⊢Type n

    infix 30 ⟨_∣_⟩ ⟮_∣_⟯⇒_

  open [𝔐TT/Definition::Type]

  module Variables/Type where variable
    A : ⊢Type m
    B : ⊢Type n
    C : ⊢Type k

  open Variables/Type

  module [𝔐TT/Definition::Ctx] where
    data ⊢Ctx {a : 𝓂} : 𝓂 -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
      ε : ⊢Ctx {a} a
      _∙⟮_∣_⟯ : ⊢Ctx {a} n -> ⊢Type m -> m ⟶ n -> ⊢Ctx {a} n
      _∙!_ : ⊢Ctx {a} n -> m ⟶ n -> ⊢Ctx m

    infix 32 _∙⟮_∣_⟯
    infixl 30 _∙!_


    data CtxExt : (m ⟶ n) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
      ε : CtxExt {m} {m} id
      _∙⟮_∣_⟯ : CtxExt {n} {k} η -> ⊢Type m -> (μ : m ⟶ n) -> CtxExt η
      _∙!_ : CtxExt {n} {k} η -> (ω : m ⟶ n) -> CtxExt (ω ◆ η)

    Mod-Ctx : (μs : Path _⟶ᵘ_ m n) -> (Γ : ⊢Ctx {k} n) -> ⊢Ctx {k} m
    Mod-Ctx id' Γ = Γ
    Mod-Ctx (μ ⨾ μs) Γ = Mod-Ctx μs Γ ∙! μ

  open [𝔐TT/Definition::Ctx]

  ft : CtxExt {m = m} {n = n} μ -> ⊢Ctx {n} m
  ft ε = ε
  ft (Γ ∙⟮ x ∣ μ ⟯) = ft Γ ∙⟮ x ∣ μ ⟯
  ft (Γ ∙! ω) = ft Γ ∙! ω

  private variable
    E F G : CtxExt μ

  _⋆_ : ⊢Ctx {o} k -> CtxExt {m} {k} η -> ⊢Ctx {o} m
  Γ ⋆ ε = Γ
  Γ ⋆ (E ∙⟮ x ∣ μ ⟯) = (Γ ⋆ E) ∙⟮ x ∣ μ ⟯
  Γ ⋆ (E ∙! ω) = (Γ ⋆ E) ∙! ω

  infixl 22 _⋆_


  data _⇛_ : (E : CtxExt {m} {n} μ) -> (F : CtxExt {m} {n} ν) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1 ⊔ 𝑖 ⌄ 2 ⊔ 𝑖 ⌄ 3) where
    id-⇛ : E ⇛ E
    _∙‼_ : {μ ν : m ⟶ n} -> E ⇛ F -> (ν ⟹ μ) -> E ∙! μ ⇛ F ∙! ν
    comp⁻¹-∙! : {μ₀ : m ⟶ n} {μ₁ : l ⟶ m} -> E ∙! μ₀ ∙! μ₁ ⇛ E ∙! (μ₁ ◆ μ₀)
    comp-∙! : {μ₀ : m ⟶ n} {μ₁ : l ⟶ m} -> E ∙! (μ₁ ◆ μ₀) ⇛ E ∙! μ₀ ∙! μ₁ 
    unit-∙! : {η : m ⟶ n} -> ∀{E : CtxExt η} -> E ⇛ E ∙! id
    unit⁻¹-∙! : {η : m ⟶ n} -> ∀{E : CtxExt η} -> E ∙! id ⇛ E
    _∙⟮_∣_⟯ : E ⇛ F -> (A : ⊢Type k) -> ∀ μ -> E ∙⟮ A ∣ μ ⟯ ⇛ F ∙⟮ A ∣ μ ⟯
    _⨾_ : E ⇛ F -> F ⇛ G -> E ⇛ G


  module Variables/Ctx where variable
    Γ : ⊢Ctx m
    Δ : ⊢Ctx n
    Ε : ⊢Ctx o

  open Variables/Ctx


  module [𝔐TT/Definition::Term] where
    data _⊢Var⟮_∣_⇒_⟯ : (Γ : ⊢Ctx {k} o) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) → 𝒰 𝑖 where
      zero : {μ : m ⟶ l} -> (Γ ∙⟮ A ∣ μ ⟯) ⊢Var⟮ A ∣ μ ⇒ id ⟯
      suc! : {μ : m ⟶ l} {η : k ⟶ l} {ω : o ⟶ k} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙! ω ⊢Var⟮ A ∣ μ ⇒ ω ◆ η ⟯
      suc : Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙⟮ B ∣ ω ⟯ ⊢Var⟮ A ∣ μ ⇒ η ⟯

    -- Sometimes when we inductively produce `⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯` proofs, the arrow's target
    -- is not strictly equal to ν₁, but only equal in the setoid on arrows. So we relax the
    -- `⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯` data type a bit.
    record _⊢Var⟮_∣_⇒∼_⟯ (Γ : ⊢Ctx {k} o) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) : 𝒰 𝑖 where
      constructor varOver
      field target : o ⟶ l
      field fst : Γ ⊢Var⟮ A ∣ μ ⇒ target ⟯
      field snd : η ∼ target

    -- Sometimes we don't want to get a setoid-equality between arrows, but only an arrow
    -- between arrows.
    record _⊢Var⟮_∣_⇒⇒_⟯ (Γ : ⊢Ctx {k} o) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) : 𝒰 𝑖 where
      constructor varOver
      field target : o ⟶ l
      field fst : Γ ⊢Var⟮ A ∣ μ ⇒ target ⟯
      field snd : η ⟹ target

    data _⊢_ {m} : ⊢Ctx {k} m -> ⊢Type m -> 𝒰 𝑖 where
      var : ∀{μ : _ ⟶ o}
            -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯
            -> (α : μ ⟹ η)
            -> class α ≤ pureTrans This
            -> Γ ⊢ A

      -- modalities
      mod : ∀ μ -> Γ ∙! μ ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⟩
      letmod : ∀{μ : o ⟶ n} -> (ν : n ⟶ m)
            -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⟩
            -> Γ ∙⟮ A ∣ μ ◆ ν ⟯ ⊢ B
            -> Γ ⊢ B

      -- explicit transformations
      trans : ∀ {μ ν : n ⟶ m}
              -> (α : μ ⟹ ν)
              -> (class α ≤ impureTrans This)
              -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

      -- transformations monad
      pure : Γ ⊢ A -> Γ ⊢ Tr A
      seq : ∀{A : ⊢Type m} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ Tr B -> Γ ⊢ Tr B

      -- functions
      lam : Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ μ ⟯⇒ B
      app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ A -> Γ ⊢ B

      -- unit type
      tt : Γ ⊢ Unit

      -- sum types
      left : Γ ⊢ A -> Γ ⊢ Either A B
      right : Γ ⊢ B -> Γ ⊢ Either A B
      either : Γ ⊢ Either A B -> Γ ∙⟮ A ∣ id ⟯ ⊢ C -> Γ ∙⟮ B ∣ id ⟯ ⊢ C -> Γ ⊢ C

      -- list types
      [] : Γ ⊢ Lst A
      _∷_ : Γ ⊢ A -> Γ ⊢ Lst A -> Γ ⊢ Lst A
      rec-Lst : Γ ⊢ Lst A -> Γ ⊢ C -> Γ ∙⟮ A ∣ id ⟯ ∙⟮ C ∣ id ⟯ ⊢ C -> Γ ⊢ C

  open [𝔐TT/Definition::Term]

  data _⟼_ : ⊢Ctx {k} m -> ⊢Ctx {k} m -> 𝒰 𝑖 where
    id-Ctx : Γ ⟼ Γ
    _∙‼_ : ∀ (Γ : ⊢Ctx {k} n) -> {μ ν : m ⟶ n} -> μ ⟹ ν -> Γ ∙! ν ⟼ Γ ∙! μ
    _∙!_ : ∀ {Γ Δ : ⊢Ctx {k} m} -> Γ ⟼ Δ -> ∀ (μ : n ⟶ m) -> Γ ∙! μ ⟼ Δ ∙! μ
    _∙⟮_⟯ : Γ ⟼ Δ -> Γ ∙! μ ⊢ A -> Γ ⟼ Δ ∙⟮ A ∣ μ ⟯
    lift : Γ ⟼ Δ -> Γ ∙⟮ A ∣ μ ⟯ ⟼ Δ ∙⟮ A ∣ μ ⟯
    -- 𝑝 : Γ ∙⟮ A ∣ μ ⟯ ⟼ Γ
    -- _⨾_ : Γ ⟼ Δ -> Δ ⟼ Ε -> Γ ⟼ Ε

  -- We allow composition only here, not in the above, simple `⟼` datatype.
  -- The reason is that we cannot prove `Skip` for composition operations,
  -- as that would involve some ugly recursion with substitution itself.
  --
  -- Since we split out the composition of substutions into this extra datatype,
  -- we have to add the `lift` constructor above. Previously, lift could be constructed
  -- from 𝑝, composition and ∙⟮_⟯. But now it cannot, because composition lives here
  -- instead of in `⟼`.
  data _⟼*_ : ⊢Ctx {k} m -> ⊢Ctx {k} m -> 𝒰 𝑖 where
    [] : Γ ⟼* Γ
    _⨾_ : Γ ⟼* Δ -> Δ ⟼ Ε -> Γ ⟼* Ε

  record Factors (Γ : ⊢Ctx {k} m) (Γ' : ⊢Ctx n) {η : m ⟶ n} (E : CtxExt η) : 𝒰 𝑖 where
    constructor factors
    field factor-restr : m ⟶ n
    field factor-Ext : CtxExt factor-restr
    field ext : Γ' ⋆ factor-Ext ≡ Γ
    field sub : factor-Ext ⇛ E

  -- easily constructing and deconstructing proofs of `Factors`
  pattern refl-Factors δ = factors _ _ refl-≡ δ


open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

----------------------------------------------------------
-- The parametrized type theory
module _ (This : MTT 𝑖) (x a : ⟨ This .ModeTheory ⟩) where
  open 𝔐TT/Definition This
  open [𝔐TT/Definition::Term]
  open [𝔐TT/Definition::Type]
  open [𝔐TT/Definition::Ctx]
  λMTT : STT _
  λMTT = record
    { Ctx = ⊢Ctx {x} a
    ; Type = ⊢Type a
    ; Term = λ Γ X -> _⊢_ Γ X
    }

instance
  hasParamSTT:MTT : hasParamSTT (MTT 𝑖)
  hasParamSTT:MTT = record
    { Param = λ 𝒯 -> ⟨ 𝒯 .ModeTheory ⟩ ×-𝒰 ⟨ 𝒯 .ModeTheory ⟩
    ; SubParam = λ 𝒯 (x , a) -> isTargetMode 𝒯 x
    ; _at_ = λ 𝒯 (x , a) -> λMTT 𝒯 x a
    }

module _ 𝑖 where macro
  𝔐TT = #structureOn (MTT 𝑖)



{-

{-

  --------------------------------------------------------------------------------
  -- Pushing transformations down
  --------------------------------------------------------------------------------
  --
  -- When we substitute a term for a variable, we need to take the transformation
  -- annotated at the variable, and push it down into the replacement term's variables.

  -- Lemma: Assume we have a variable in (Γ ∙！ μ₀ ⋆ E). We want to change the variable
  --        to be in context (Γ ∙! μ₁ ⋆ E). There are two possible cases, and this lemma
  --        decides in which we are:
  --
  --          - Either the de-brujin index of the variable is low enough that it lives
  --            in E. Then the variable does not care about whether there is μ₀ or μ₁,
  --            and we can switch easily (case 1.).
  --
  --          - Otherwise, the variable lives in Γ. Let the variable be of type `v : (Γ ∙！ μ₀ ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯`.
  --            Thus what we have is that this variable is under all restrictions from `E`, and furthermore under `μ₀`,
  --            and maybe even under some restrictions in Γ. Since ν₁ tracks the total restriction of v, this means
  --            that ν₁ factors into (η ◆ μ₀ ◆ ϕ) where ϕ is the additional restriction in Γ. (case 2.)
  --
  decide-Var : (μ₁ : l₁ ⟶ k)
             -> {μ₀ : l₁ ⟶ k}
             -> {η : l₀ ⟶ l₁}
             -> {ν₀ : ModeHom m₀ n} {ν₁ : ModeHom l₀ n}
             -> (E : CtxExt {l₀} {l₁} η)
             -> {Γ : ⊢Ctx _}
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


  -- Weaking of a variable under a whole context extension E. Of course the variable target annotation has to
  -- be extended with η (the restriction belonging to E)
  _∙!*-Var_ : {μ : m ⟶ n} -> {η : k ⟶ _} -> Γ ⊢Var⟮ A ∣ μ ⇒ ν ⟯ -> (E : CtxExt η) -> (Γ ⋆ E) ⊢Var⟮ A ∣ μ ⇒∼ η ◆ ν ⟯
  v ∙!*-Var ε = varOver _ v (unit-l-◆)
  v ∙!*-Var (E ∙⟮ x ∣ μ ⟯) = let varOver _ v' p = (v ∙!*-Var E) in varOver _ (suc v') p
  v ∙!*-Var (E ∙! ω) = let varOver _ v' p = (v ∙!*-Var E) in varOver _ (suc! v') (assoc-l-◆ ∙ (refl-∼ ◈ p))


  -- We have a variable `v : ((Γ ∙! μ) ⋆ E) ⊢Var⟮ A ∣ η ⇒ ω ⟯`, and a transformation `α : μ ⟹ ν`. We want to change the variable
  -- to live in a context where μ is replaced by ν. We mostly use the `decide-Var` lemma, but in its second case we have to construct
  -- a slightly elaborate transformation as new annotation at the variable.
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

  -- Finally, after having shown that we can push an annoation onto a variable, we now
  -- can push annoations down onto a full term. Inductive, in some cases we have to
  -- alter the transformation as it is pushed down under mod/letmod/app terms.
  pushDown : ∀ Γ (E : CtxExt η) -> {μ : _ ⟶ n} -> ((Γ ∙! μ) ⋆ E) ⊢ A -> (μ ⟹ ν) -> ((Γ ∙! ν) ⋆ E) ⊢ A
  pushDown Γ E (var x β) α = pushDown-Var x α β
  pushDown Γ E tt α = tt
  pushDown Γ E (mod μ t) α = mod μ (pushDown Γ (E ∙! μ) t α)
  pushDown Γ E (letmod ν t s) α = letmod ν (pushDown Γ (E ∙! ν) t α) (pushDown Γ (E ∙⟮ _ ∣ _ ⟯) s α)
  pushDown Γ E (lam t) α = lam (pushDown _ _ t α)
  pushDown Γ E (app t s) α = app (pushDown Γ E t α) (pushDown Γ (E ∙! _) s α)



  --------------------------------------------------------------------------------
  -- Applying ⇛-transformations to terms.
  --------------------------------------------------------------------------------
  -- These ⇛ transformations have two purposes:
  --  - They occur as the result of the `Skip` lemma, and have to be applied to
  --    a term in the var-case of substition.
  --  - They also encode the fact that for example Γ.{id}≡Γ or Γ.{μ}.{ν}≡Γ.{ν;μ}.
  --

  -- The main lemma, applying a ⇛-transformation to a variable.
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

  -- We can apply a ⇛-transformation also under a (_⋆ F) context extension.
  map-Var-cong : {E₀ : CtxExt η₀} {E₁ : CtxExt η₁} -> E₁ ⇛ E₀ -> (F : CtxExt ω)
                    -> (Γ ⋆ E₀ ⋆ F) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
                    -> (Γ ⋆ E₁ ⋆ F) ⊢Var⟮ A ∣ ν₀ ⇒⇒ ν₁ ⟯
  map-Var-cong ξ ε v = map-Var ξ v
  map-Var-cong ξ (F ∙⟮ x ∣ μ ⟯) zero = varOver _ zero id
  map-Var-cong ξ (F ∙⟮ x ∣ μ ⟯) (suc v) = let varOver _ v' p = map-Var-cong ξ F v in varOver _ (suc v') p
  map-Var-cong ξ (F ∙! ω) (suc! v) = let varOver _ v' p = map-Var-cong ξ F v in varOver _ (suc! v') (id ⇃◆⇂ p)

  -- Applying ⇛-transformations on terms is done inductively of course.
  map-cong : {E₀ : CtxExt η₀} {E₁ : CtxExt η₁} -> E₁ ⇛ E₀ -> (F : CtxExt ω)
                    -> (Γ ⋆ E₀ ⋆ F) ⊢ A
                    -> (Γ ⋆ E₁ ⋆ F) ⊢ A
  map-cong ξ F (var x α) = let varOver _ v p = map-Var-cong ξ F x in var v (α ◆ p )
  map-cong ξ F tt = tt
  map-cong ξ F (mod μ t) = mod μ (map-cong ξ (F ∙! μ) t)
  map-cong ξ F (letmod ν t s) = letmod ν (map-cong ξ (F ∙! ν) t) (map-cong ξ (F ∙⟮ _ ∣ _ ⟯) s)
  map-cong ξ F (lam t) = lam (map-cong ξ (F ∙⟮ _ ∣ _ ⟯) t)
  map-cong ξ F (app t s) = app (map-cong ξ F t) (map-cong ξ (F ∙! _) s)


  -- Some abbreviations for applying commong ⇛-Transformations
  map-comp-∙! : ∀{μ : n ⟶ o} {ω : m ⟶ n} -> Γ ∙! μ ∙! ω ⊢ A -> Γ ∙! (ω ◆ μ) ⊢ A
  map-comp-∙! {Γ = Γ} = map-cong {Γ = Γ} comp-∙! ε

  map-comp⁻¹-∙! : ∀{μ : n ⟶ o} {ω : m ⟶ n} -> Γ ∙! (ω ◆ μ) ⊢ A -> Γ ∙! μ ∙! ω ⊢ A
  map-comp⁻¹-∙! {Γ = Γ} = map-cong {Γ = Γ} comp⁻¹-∙! ε

  map-unit-∙! : ∀{Γ : ⊢Ctx k} -> Γ ∙! id ⊢ A -> Γ ⊢ A
  map-unit-∙! {Γ = Γ} = map-cong {Γ = Γ} unit-∙! ε

  map-unit⁻¹-∙! :  ∀{Γ : ⊢Ctx k} -> Γ ⊢ A -> Γ ∙! id ⊢ A
  map-unit⁻¹-∙! {Γ = Γ} = map-cong {Γ = Γ} unit⁻¹-∙! ε


  --------------------------------------------------------------------------------
  -- WEAKENING
  --------------------------------------------------------------------------------
  -- The key insight is that we cannot add new restrictions to a term when weakening
  -- so the statement of weakening is slightly adapted. We say that we can extend a context Γ
  -- by an extraneous list of variables from `E : CtxExt η` if previously, Γ was restricted by
  -- η (see wk!).

  -- Single weakening (for variable). We use context extensions to be able to weaken at an arbitrary
  -- position in the context.
  wk-Var : ∀ (E : CtxExt η) -> (Γ ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯ -> (Γ ∙⟮ B ∣ μ ⟯ ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
  wk-Var ε v = suc v
  wk-Var (E ∙⟮ x ∣ μ ⟯) zero = zero
  wk-Var (E ∙⟮ x ∣ μ ⟯) (suc v) = suc (wk-Var E v)
  wk-Var (E ∙! ω) (suc! v) = suc! (wk-Var E v)

  -- Single weakening.
  wk : ∀ (E : CtxExt η) -> (Γ ⋆ E) ⊢ A -> (Γ ∙⟮ B ∣ μ ⟯ ⋆ E) ⊢ A
  wk E (var x α) = var (wk-Var E x) α
  wk E tt = tt
  wk E (mod μ t) = mod μ (wk (E ∙! μ) t)
  wk E (letmod ν t s) = letmod ν (wk (E ∙! ν) t) (wk (E ∙⟮ _ ∣ _ ⟯) s)
  wk E (lam t) = lam (wk (E ∙⟮ _ ∣ _ ⟯) t)
  wk E (app t s) = app (wk E t) (wk (E ∙! _) s)

  -- Weakening of terms, the induction
  wk!-ind : ∀(E : CtxExt η) -> ∀ μ -> (Γ ∙! η) ∙! μ ⊢ A -> (Γ ⋆ E) ∙! μ ⊢ A
  wk!-ind {Γ = Γ} ε μ t = map-cong {Γ = Γ} ((id-⇛ ∙‼ υ-r-◆) ⨾ comp-∙!) ε t
  wk!-ind (E ∙⟮ x ∣ ν ⟯) μ t = let X = wk!-ind E μ t in wk (ε ∙! μ) X
  wk!-ind {Γ = Γ} (E ∙! ω) μ t =
    let res : Γ ⋆ E ∙! (μ ◆ ω) ⊢ _
        res = (wk!-ind E (μ ◆ ω) (map-cong {Γ = Γ} ((comp⁻¹-∙! ⨾ (id-⇛ ∙‼ α-r-◆)) ⨾ comp-∙!) ε t))
    in map-cong {Γ = Γ ⋆ E} {E₀ = (ε ∙! (μ ◆ ω))} {E₁ = (ε ∙! ω ∙! μ)} comp⁻¹-∙! ε res

  -- simplified.
  wk! : ∀(E : CtxExt η) -> (Γ ∙! η) ⊢ A -> (Γ ⋆ E) ⊢ A
  wk! E t = map-unit-∙! (wk!-ind E id (map-unit⁻¹-∙! t))



  -- Our famous skip lemma.
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


  -- Finally we can state substition, we use all our ingredients in the var-case in order to:
  --  - extract the term for our current variable from δ by using `Skip`. The term is typed
  --    not in the full context, but in a smaller context Γ'.
  --  - use `pushDown` to push the variable's transformation down this term
  --  - use `wk!` to weaken the term in order to include the context extension E which was
  --    "skipped" by `Skip`
  --  - use map-cong to apply the ⇛-transformation which fell out from `Skip`.
  -- Done!
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




-}


-}

