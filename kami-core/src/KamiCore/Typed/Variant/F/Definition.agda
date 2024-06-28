
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Definition where

open import Agora.Conventions hiding (m ; n ; _∙_ ; _∣_)
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

  private variable
    m n o p : 𝓂 {{Param}}
    μ : Hom {{of 𝓂'}} m n
    ν : Hom {{of 𝓂'}} n o

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

  private variable
    Γ : Ctx m
    Δ : Ctx n

  data _⊢_ : Ctx m -> ⊢Type m -> 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1) where
    var : Γ ∙⟮ A ∣ μ ⟯ ∙! μ ⊢ A
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


open import Agora.TypeTheory.Notation

instance
  isTypeTheory:MTTꟳ : isTypeTheory (MTTꟳ 𝑖)
  isTypeTheory:MTTꟳ = record
    { ⊢Ctx = Definition-MTTꟳ.Ctx
    ; ⊢Type = Definition-MTTꟳ.⊢Type
    ; _⊢_ = λ {{a}} -> λ {m : 𝓂} -> Definition-MTTꟳ._⊢_ {m = m}
    }

-- instance
--   isSimpleTypeTheory:MTTꟳ : isSimpleTypeTheory (MTTꟳ 𝑖)
--   isSimpleTypeTheory:MTTꟳ = record
--     { Param = λ P -> 𝓂 {{P}}
--     ; Ctx = λ {T} p -> Definition-MTTꟳ.Ctx {{T}} p
--     ; Type = λ {T} p -> Definition-MTTꟳ.⊢Type {{T}} p
--     ; Term = λ {T} {p} Γ X -> Definition-MTTꟳ._⊢_ {{T}} Γ X
--     }

-- module _ {𝒯 : MTTꟳ 𝑖} where
--   instance
--     isSimpleTypeTheory:𝓂 : isSimpleTypeTheory (𝓂 {{𝒯}})
--     isSimpleTypeTheory:𝓂 = record
--       { Ctx = Definition-MTTꟳ.Ctx {{𝒯}}
--       ; Type = Definition-MTTꟳ.⊢Type {{𝒯}}
--       ; Term = λ Γ X -> Definition-MTTꟳ._⊢_ {{𝒯}} Γ X
--       }

module _ (𝒯 : MTTꟳ 𝑖) (a : 𝓂 {{𝒯}}) where
  λMTTꟳ : SimpleTypeTheory
  λMTTꟳ = record
    { Ctx = Definition-MTTꟳ.Ctx {{𝒯}} a
    ; Type = Definition-MTTꟳ.⊢Type {{𝒯}} a
    ; Term = λ Γ X -> Definition-MTTꟳ._⊢_ {{𝒯}} Γ X
    }

instance
  isSTTFamily:MTTꟳ : isParametrizedSTT (MTTꟳ 𝑖)
  isSTTFamily:MTTꟳ = record
    { Param = λ 𝒯 -> 𝓂 {{𝒯}}
    ; _at_ = λMTTꟳ
    }

module _ {𝒯 : MTTꟳ 𝑖} where
  testt1 : ∀{m : Param 𝒯} -> (Γ : Ctx m of 𝒯) -> Ctx m of 𝒯
  testt1 = {!!}


-- module _ {{𝒯 : MTTꟳ 𝑖}} {a b : ℕ} where
--   -- testt1 : ∀{m : Param 𝒯} -> (Γ : Ctx m of 𝒯) -> Ctx m of 𝒯
--   testt1 : ∀{m : Param 𝒯} -> (Γ : Ctx {{isSimpleTypeTheory:MTTꟳ}} m) -> Ctx m of 𝒯
--   testt1 = {!!}


module _ {{mtt : MTTꟳ 𝑖}} {a b : ℕ} where
  testss : {m : 𝓂} -> (Γ : [ mtt ]-Ctx m) -> ∀{A : ⊢Type m} -> Γ ⊢ A
  testss = {!!}



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

