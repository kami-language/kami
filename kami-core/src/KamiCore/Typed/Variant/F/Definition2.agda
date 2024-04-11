
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Definition2 where

open import Agora.Conventions hiding (m ; n ; k ; _∣_)
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.Category.Std.Functor.Definition
open import Agora.Category.Std.Natural.Definition

-- open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
-- open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition -- hiding (_◆_)
-- open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition

open import Data.Vec

-- open 2CellDefinition
-- open ModeSystem

-- module _ {𝓂 : 𝒰 _} {{𝓂p : 2Category 𝑖 on 𝓂}} where
-- module _ {𝓂 : 𝒰 _} {{𝓂p : 2Category 𝑖 on 𝓂}} where



record MTTꟳ (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  field 𝓂 : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:𝓂}} : isCategory {𝑖 ⌄ 1 ⋯ 2} 𝓂
  field {{is2Category:𝓂}} : is2Category {𝑖 ⌄ 3 ⋯ 4} ′ 𝓂 ′

open MTTꟳ {{...}} public



module _ where
  open import Agora.Conventions.Meta.Term
  open import Agora.Conventions.Meta.Universe

  _/_ : ∀{A : 𝒰 𝑖} -> {F : {a : A} -> 𝒰 𝑘} -> (B : {{a : A}} -> F {a}) -> (a : A) -> F {a}
  _/_ B a = B {{a}}

  applyInnermost : Term -> TC 𝟙-𝒰
  applyInnermost (def n args) = return tt
  applyInnermost t = printErr ("is not application: " <> show t)

  replaceFirstInstanceArg : (termWithLams : Term) -> (replacement : Term) -> TC Term
  replaceFirstInstanceArg t0@(lam instance′ (abs varname t)) r = do
    let t' = tesubst (0 , λ args -> r) t
    return t'
    -- printErr ("input: " <> show t0 <> "\nreplacement: " <> show r <> "\nresult term: " <> show t')

  --   `T` <- inferType `t`
  --   ``
  --   quoteTC (`t` {{r}})

  replaceFirstInstanceArg (lam v (abs varname rest)) r = do
    res <- replaceFirstInstanceArg rest (liftFrom 0 r)
    -- return (lam v (Abs.abs varname res))

    let res' = (lowerAt 0 res)
    return res' -- (lam v (Abs.abs varname res))
  replaceFirstInstanceArg t r = printErr ("is not application: " <> show t)

  macro
    _from_ : Term -> Term -> Term -> TC 𝟙-𝒰
    _from_ app insert hole = do
      app' <- withReconstructed true (normalise app)
      res <- replaceFirstInstanceArg app' insert
      -- res' <- withReconstructed true (normalise res)
      unify hole res


-- module _ {𝓂 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝓂}} {{_ : is2Category {𝑘} ′ 𝓂 ′}} where
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

  data CtxExt : {m n : 𝓂} -> (m ⟶ n) -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    ε : CtxExt {m} {m} id
    _∙⟮_∣_⟯ : CtxExt {n} {k} η -> ⊢Type m -> (μ : m ⟶ n) -> CtxExt η
    _∙!_ : CtxExt {n} {k} η -> (ω : m ⟶ n) -> CtxExt (ω ◆ η)

  private variable
    E F : CtxExt μ

  _⋆_ : Ctx k -> CtxExt {m} {k} η -> Ctx m
  Γ ⋆ ε = Γ
  Γ ⋆ (E ∙⟮ x ∣ μ ⟯) = (Γ ⋆ E) ∙⟮ x ∣ μ ⟯
  Γ ⋆ (E ∙! ω) = (Γ ⋆ E) ∙! ω

  data _⇛_ : (E : CtxExt {m} {n} μ) -> (F : CtxExt {m} {n} ν) -> 𝒰 𝑖 where
    id-⇛ : E ⇛ E
    _∙‼_ : {μ ν : m ⟶ n} -> E ⇛ F -> (ν ⟹ μ) -> E ∙! μ ⇛ F ∙! ν
    _∙⟮_∣_⟯ : E ⇛ F -> (A : ⊢Type k) -> ∀ μ -> E ∙⟮ A ∣ μ ⟯ ⇛ F ∙⟮ A ∣ μ ⟯



  private variable
    Γ : Ctx m
    Δ : Ctx n

  data _⊢Var⟮_∣_⇒_⟯ : (Γ : Ctx k) (A : ⊢Type m) (μ : m ⟶ l) (η : o ⟶ l) → 𝒰 𝑖 where
    zero : ∀{Γ} {μ : m ⟶ l} -> (Γ ∙⟮ A ∣ μ ⟯) ⊢Var⟮ A ∣ μ ⇒ id ⟯
    suc! : ∀{Γ} {μ : m ⟶ l} {η : k ⟶ l} {ω : o ⟶ k} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙! ω ⊢Var⟮ A ∣ μ ⇒ ω ◆ η ⟯
    suc : Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> Γ ∙⟮ B ∣ ω ⟯ ⊢Var⟮ A ∣ μ ⇒ η ⟯


  data _⊢_ : Ctx m -> ⊢Type m -> 𝒰 𝑖 where
    var : ∀{μ : _ ⟶ o} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
    tt : Γ ⊢ Unit
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

  record Factors (Γ : Ctx m) (Γ' : Ctx n) {η : m ⟶ n} (E : CtxExt η) : 𝒰 𝑖 where
    constructor factors
    field factor-restr : m ⟶ n
    field factor-Ext : CtxExt factor-restr
    field ext : Γ' ⋆ factor-Ext ≡ Γ
    field sub : factor-Ext ⇛ E

  -- refl-Factors : ∀{Γ' : Ctx n} -> {η : m ⟶ n} {E : CtxExt η} -> Factors (Γ' ⋆ E) Γ' E
  -- refl-Factors = factors _ _ refl-≡ id-⇛

  pattern refl-Factors δ = factors _ _ refl-≡ δ

  Skip : ∀ Γ Δ -> Γ ⟼ Δ -> {η : k ⟶ l} -> Δ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> ∑ λ Γ' -> ∑ λ (E : CtxExt η) -> (Γ' ∙! μ ⊢ A) ×-𝒰 Factors Γ Γ' E
  Skip _ .(_ ∙⟮ _ ∣ _ ⟯) (id-Ctx {Γ = Γ ∙⟮ A ∣ μ ⟯}) zero = Γ ∙⟮ A ∣ μ ⟯ , ε , var (suc! zero) {!!} , {!!}
  Skip Γ .(_ ∙⟮ _ ∣ _ ⟯) (_∙⟮_∣_⟯ δ x) zero = Γ , ε , x , refl-Factors id-⇛
  Skip (Γ ∙! x) (.Γ ∙! .x) id-Ctx (suc! v) with
    (Γ' , E , t , refl-Factors γ) <- Skip Γ _ id-Ctx v
    = Γ' , (E ∙! x) , t , refl-Factors (γ ∙‼ id {{2HomData}})
  Skip (Γ ∙! x) (.Γ ∙! y) (.Γ ∙‼ α) (suc! v) with
    (Γ' , E , t , refl-Factors γ) <- Skip Γ _ id-Ctx v
    = Γ' , (E ∙! y) , t , refl-Factors (γ ∙‼ α)
  Skip (Γ ∙! x) (Δ ∙! .x) (_∙!_ δ) (suc! v) with
    (Γ' , E , t , refl-Factors γ) <- Skip Γ Δ δ v
    = Γ' , (E ∙! x) , t , refl-Factors (γ ∙‼ id {{2HomData}})
  Skip .(_ ∙⟮ _ ∣ _ ⟯) .(_ ∙⟮ _ ∣ _ ⟯) id-Ctx (suc v) with -- = {!!} -- Skip _ _ id-Ctx v
    (Γ' , E , t , refl-Factors γ) <- Skip _ _ id-Ctx v
    = Γ' , _ , t , refl-Factors (γ ∙⟮ _ ∣ _ ⟯) --- (γ ∙‼ id {{2HomData}})
  Skip Γ .(_ ∙⟮ _ ∣ _ ⟯) (_∙⟮_∣_⟯ δ x) (suc v) = Skip _ _ δ v

  decide-Var : (μ₁ : l₁ ⟶ k)
             -> {μ₀ : l₁ ⟶ k}
             -> {η : l₀ ⟶ l₁}
             -> {ν₀ : ModeHom m₀ n} {ν₁ : ModeHom m₁ n}
             -> (E : CtxExt {l₀} {l₁} η)
             -> {Γ : Ctx _}
             -> ((Γ ∙! μ₀) ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯
             -> (((Γ ∙! μ₁) ⋆ E) ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯)
                +-𝒰 (∑ λ (ϕ₀ : m₁ ⟶ l₀) -> ∑ λ (ν₂ : l₁ ⟶ n) -> (Γ ∙! μ₀) ⊢Var⟮ A ∣ ν₀ ⇒ ν₂ ⟯ ×-𝒰 ϕ₀ ◆ η ◆ ν₂ ∼ ν₁)
  decide-Var ν {ν₁ = ν₁} ε v = right ({!!} , {!!} , {!!} , {!!})
  -- decide-Var ν {ν₁ = ν₁} ε v = right (_ , id , ν₁ , v , unit-l-◆ )
  decide-Var ν (E ∙⟮ x ∣ μ ⟯) zero = left zero
  decide-Var ν (E ∙⟮ x ∣ μ ⟯) (suc v) with decide-Var ν E v
  ... | no v = no (suc v)
  ... | yes v = yes v
  decide-Var μ₁ {μ₀} {η'} {ν₀} {ν₁} (_∙!_ {η = η} E ω) (suc! {η = η₁} {ω = ω} v) with decide-Var μ₁ {μ₀} {η} {ν₀}  E v
  ... | no v = no (suc! v)
  ... | yes X = {!!} -- (_ , ϕ₀ , ϕ₁ , t , p) = yes ((_ , ω ◆ ϕ₀ , ϕ₁ , t , {!!} )) -- assoc-l-◆ ∙ (refl-∼ ◈ p)))

  transform-Var : {μ : m ⟶ n} {ν₁ : k ⟶ l} -> Γ ∙! μ ⊢Var⟮ A ∣ ν₀ ⇒ ν₁ ⟯ -> (μ ⟹ ν) -> ∑ λ (ν₂ : k ⟶ l) -> Γ ∙! μ ⊢Var⟮ A ∣ ν₀ ⇒ ν₂ ⟯
  transform-Var (suc! t) α = _ , suc! t

  pushDown-Var : {η₀ : _ ⟶ k} {ν : _ ⟶ _} {E : CtxExt η₀} -> {μ : _ ⟶ n} {η : m₀ ⟶ m₁} {ω : m₀ ⟶ m₁} -> ((Γ ∙! μ) ⋆ E) ⊢Var⟮ A ∣ η ⇒ ω ⟯ -> (μ ⟹ ν) -> (η ⟹ ω) -> ((Γ ∙! ν) ⋆ E) ⊢ A
  pushDown-Var {ν = ν} {E = E} v α β with decide-Var ν E v
  ... | no x = var x β
  ... | yes ( ϕ₀ , ϕ₁ , (suc! t) , p) = let _ , v = transform-Var (suc! t) α in {!!} 



  pushDown : {μ : _ ⟶ n} -> ((Γ ∙! μ) ⋆ E) ⊢ A -> (μ ⟹ ν) -> ((Γ ∙! ν) ⋆ E) ⊢ A
  pushDown (var x β) α = pushDown-Var x α {!!}
  pushDown tt α = {!!}
  pushDown (mod t) α = {!!}
  pushDown (letmod t t₁) α = {!!}
  pushDown (lam t) α = lam (pushDown t α)
  pushDown (app t t₁) α = {!!}

  _[_] : Δ ⊢ A -> (δ : Γ ⟼ Δ) -> Γ ⊢ A
  var x α [ δ ] =
    let Γ' , E , t , P = Skip _ _ δ x
        t' = pushDown {E = ε} t α
    in {!!}
  tt [ δ ] = tt
  mod t [ δ ] = {!!}
  letmod t t₁ [ δ ] = {!!}
  lam t [ δ ] = {!!}
  app t t₁ [ δ ] = {!!}

  -- _[_]-Var : {μ : _ ⟶ n} {η : _ ⟶ _} {A : ⊢Type m} {Δ : Ctx k} -> Δ ⊢Var⟮ A ∣ μ ⇒ η ⟯ ×-𝒰 (μ ⟹ ω ◆ η) -> (δ : Γ ⟼ Δ) -> Γ ⊢ B
  -- (v , α) [ id-Ctx ]-Var = {!!}
  -- (v , α) [ Γ ∙‼ x ]-Var = {!!}
  -- (suc! v , α) [ _∙!_ δ ]-Var = let X = _[_]-Var (v , {!α!}) δ in {!!}
  -- (v , α) [ _∙⟮_∣_⟯ δ x ]-Var = {!!}


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
