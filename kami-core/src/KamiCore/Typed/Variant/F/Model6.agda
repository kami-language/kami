
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model6 where

open import Agora.Conventions hiding (k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition



record isProcessSet 𝑗 : 𝒰 (𝑗 ⁺) where
  field Proc : StrictOrder 𝑗
  -- field all : ⟨ L ⟩
  -- field split : ⟨ L ⟩ -> 𝒫ᶠⁱⁿ Proc
  -- field re : ⟨ Proc ⟩ -> ⟨ L ⟩

  instance
    hasDecidableEquality:Proc : hasDecidableEquality ⟨ Proc ⟩
    hasDecidableEquality:Proc = hasDecidableEquality:byStrictOrder

open isProcessSet public using (Proc)
-- open isProcessSet {{...}} public using (split ; re ; all ; hasDecidableEquality:Proc)







-- module _ (I : 𝒰 𝑖) where
data ComType : 𝒰₀ where
  ℂ : ComType
  Unit : ComType
  _××_ : ComType -> ComType -> ComType
  _⇒_ : ComType -> ComType -> ComType

infixr 30 _××_ _⇒_

data _⊢Var_Com : ComType -> ComType -> 𝒰₀ where
  zero : ∀{Γ} -> Γ ⊢Var Γ Com
  sucr : ∀{Γ A B} -> Γ ⊢Var A Com -> (Γ ×× B) ⊢Var A Com
  sucl : ∀{Γ A B} -> Γ ⊢Var A Com -> (B ×× Γ) ⊢Var A Com

module _ {I : 𝒰 𝑖} {f : I -> ComType} where
  data _⊢_Com : ComType -> ComType -> 𝒰 𝑖 where
    var : ∀{Γ A} -> Γ ⊢Var A Com -> Γ ⊢ A Com
    _,_ : ∀{Γ A B} -> Γ ⊢ A Com -> Γ ⊢ B Com -> Γ ⊢ A ×× B Com
    lam : ∀{Γ A B} -> (Γ ×× A) ⊢ B Com -> Γ ⊢ A ⇒ B Com
    app : ∀{Γ A B} -> Γ ⊢ A ⇒ B Com -> Γ ⊢ A Com -> Γ ⊢ B Com
    𝟘 : ∀{Γ} -> Γ ⊢ ℂ Com
    tt : ∀{Γ} -> Γ ⊢ Unit Com
    com : ∀{Γ} -> (i : I) -> Γ ⊢ f i Com -> Γ ⊢ ℂ Com
    _≫_ : ∀{Γ} -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ Com

    -- _≫-↷_ : ∀{Γ A} -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ ×× A Com -> Γ ⊢ ℂ ×× A Com

    _⊹_ : ∀{Γ} -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ Com


_⊢_Com[_] : ComType -> ComType -> {I : 𝒰 𝑖} -> (I -> ComType) -> 𝒰 𝑖
_⊢_Com[_] A B f = _⊢_Com {f = f} A B



-- module IR {Loc : Preorder 𝑖} {{_ : hasFiniteMeets Loc}} (split : 𝒫ᶠⁱⁿ (Proc L) -> 𝒫ᶠⁱⁿ (Proc L)) where
-- module IR {Loc : Preorder 𝑖} {{L : isProcessSet 𝑗}} where
module IR {{L : isProcessSet 𝑗}} where

  private variable
    -- k l : 𝒫ᶠⁱⁿ (Proc L)
    k l ks ls : 𝒫ᶠⁱⁿ (Proc L)
    p q : ⟨ Proc L ⟩


  data ▲Type : 𝒰 (𝑗)
  data ▲Type₊ : 𝒰 (𝑗)
  data ◯Type : 𝒰 (𝑗)
  data ◯Type₊ : 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)
  -- data Com : 𝒰 𝑖

  -- data ▲Ann : ▲Type -> 𝒰 𝑖
  -- data ◯Ann : ◯Type -> 𝒰 𝑖



  data ▲Type where
    ◻ : ◯Type -> ▲Type
    NN : ▲Type
    Unit : ▲Type
    Either : ▲Type -> ▲Type -> ▲Type
    _⇒_ : ▲Type -> ▲Type -> ▲Type
    Wrap : ▲Type -> ▲Type

  data ▲Type₊ where
    ◻ : ◯Type₊ l -> ▲Type₊
    NN : ▲Type₊
    Unit : ▲Type₊
    Either : ▲Type₊ -> ▲Type₊ -> ▲Type₊
    _⇒_ : ▲Type₊ -> ▲Type₊ -> ▲Type₊

  pattern BB = Either Unit Unit


  data ◯Type where
    _＠_ : ▲Type -> (l : 𝒫ᶠⁱⁿ (Proc L)) -> ◯Type
    _⇒_ : ◯Type -> ◯Type -> ◯Type
    Either : ◯Type -> ◯Type -> ◯Type
    Wrap : ◯Type -> ◯Type

  data ◯Type₊ where
    _＠_ : ▲Type₊ -> (l : 𝒫ᶠⁱⁿ (Proc L)) -> ◯Type₊ l
    _⇒_ : ◯Type₊ l -> ◯Type₊ l -> ◯Type₊ l

  infix 30 _＠_
  -- infix 45 _⇒_


  -- data Ctx : 𝒰 𝑖 where
  --   ε : Ctx
  --   _,_©_ : Ctx -> ◯Type₊ l -> Com -> Ctx

  -- infixl 30 _,_©_


  -- data ▲Ctx : 𝒰 𝑖 where
  --   ε : ▲Ctx
  --   _,_©_ : ▲Ctx -> ▲Type -> Com -> ▲Ctx

  data Ctx : 𝒰 (𝑗) where
    ε : Ctx
    _,_ : Ctx -> ◯Type -> Ctx


  data isLocal (l : 𝒫ᶠⁱⁿ (Proc L)) : Ctx -> 𝒰 (𝑗) where
    ε : isLocal l ε
    step : ∀{Γ A} -> isLocal l Γ -> isLocal l (Γ , A ＠ l)


  ⟦_⟧-◯Type : ◯Type -> ComType

  private variable
    -- Ξ : ▲Ctx
    Γ Δ : Ctx
    X Y Z : ◯Type
    -- X₊ Y₊ Z₊ : ◯Type₊ l
    A B C D : ▲Type
    x y z : ComType
    -- A₊ B₊ C₊ D₊ : ▲Type₊
    δ δ₀ δ₁ : x ⊢ y Com[ ⟦_⟧-◯Type ]
    ζ ζ₀ ζ₁ : x ⊢ y Com[ ⟦_⟧-◯Type ]
    c d : x ⊢ ℂ Com[ ⟦_⟧-◯Type ]


  ---------------------------------------------

  data _∣_↦_Type : ◯Type -> ⟨ Proc L ⟩ -> ▲Type -> 𝒰 (𝑗) where
    -- proj-＠ : ∀{k} -> l ≤ re k -> A ＠ l ∣ k ↦ A
    -- proj-＠-≠ : ∀{k} -> (¬ l ≤ re k) -> A ＠ l ∣ k ↦ Unit
    _⇒_ : X ∣ p ↦ A Type -> Y ∣ p ↦ B Type -> (X ⇒ Y) ∣ p ↦ (A ⇒ B) Type


  data _∣_↦_Ctx : Ctx -> (l : ⟨ Proc L ⟩) -> ∑ isLocal ⦗ l ⦘ -> 𝒰 (𝑗) where
    ε : ε ∣ p ↦ (ε , ε) Ctx
    _,_ : ∀{Δp} -> Γ ∣ p ↦ Δ , Δp Ctx -> X ∣ p ↦ A Type -> Γ , X ∣ p ↦ (Δ , A ＠ ⦗ p ⦘) , step Δp Ctx


  ---------------------------------------------

  _⊹-Com_ : (δ₀ δ₁ : x ⊢ y Com[ ⟦_⟧-◯Type ]) -> x ⊢ y Com[ ⟦_⟧-◯Type ]
  _⊹-Com_ {y = ℂ} d e = d ⊹ e
  _⊹-Com_ {y = Unit} d e = tt
  _⊹-Com_ {y = y₀ ×× y₁} d e = {!!}
  _⊹-Com_ {y = y ⇒ y₁} d e = {!!}


  ⟦_⟧₊-◯Type : ◯Type -> ComType
  ⟦_⟧-▲Type : ▲Type -> ComType
  ⟦ ◻ x ⟧-▲Type = ⟦ x ⟧-◯Type
  ⟦ NN ⟧-▲Type = {!!}
  ⟦ Unit ⟧-▲Type = {!!}
  ⟦ Either A A₁ ⟧-▲Type = {!!}
  ⟦ A ⇒ B ⟧-▲Type = ⟦ A ⟧-▲Type ⇒ ⟦ B ⟧-▲Type
  ⟦ Wrap A ⟧-▲Type = ℂ ×× ⟦ A ⟧-▲Type

  ⟦_⟧₊-◯Type X = ℂ ×× ⟦ X ⟧-◯Type
  ⟦ x ＠ _ ⟧-◯Type = ⟦ x ⟧-▲Type
  ⟦ X ⇒ Y ⟧-◯Type = ⟦ X ⟧-◯Type ⇒ ⟦ Y ⟧-◯Type
  ⟦ Either X Y ⟧-◯Type = ⟦ X ⟧-◯Type ×× ⟦ Y ⟧-◯Type
  ⟦ Wrap X ⟧-◯Type = ℂ ×× ⟦ X ⟧-◯Type

  ⟦_⟧-Ctx : Ctx -> ComType
  ⟦ ε ⟧-Ctx = Unit
  ⟦ Γ , x ⟧-Ctx = ⟦ Γ ⟧-Ctx ×× ⟦ x ⟧-◯Type


  data _⊢_/_Global : (Γ : Ctx) -> (X : ◯Type) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ X ⟧-◯Type Com[ ⟦_⟧-◯Type ] -> 𝒰 (𝑗) where
    lam : Γ , X ⊢ Y / δ Global -> Γ ⊢ X ⇒ Y / (lam δ) Global

    app : Γ ⊢ X ⇒ Y / (δ₀) Global
        -> Γ ⊢ X / δ₁ Global
        -> Γ ⊢ Y / app δ₀ δ₁ Global

   -- seq : Γ ⊢ X / (c , δ₀) Global
    --     -> Γ , X ⊢ Y / δ₁ Global
    --     -> Γ ⊢ Y / c ≫-↷ (app (lam δ₁) (𝟘 , δ₀)) Global

    left : Γ ⊢ X / δ₀ Global
         -> Γ ⊢ Either X Y / (δ₀ , δ₁) Global


    either : Γ ⊢ Either X Y / (δ₀ , δ₁) Global
             -> Γ , X ⊢ Z / ζ₀ Global
             -> Γ , Y ⊢ Z / ζ₁ Global
             -> Γ ⊢ Z / (app (lam ζ₀) δ₀ ⊹-Com app (lam ζ₁) δ₁) Global


  data _⊢_/_GlobalFiber[_] : (Γ : Ctx) -> (A : ▲Type) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ A ⟧-▲Type Com[ ⟦_⟧-◯Type ] -> ⟨ Proc L ⟩ -> 𝒰 (𝑗) where
    recv : X ∣ p ↦ A Type -> Γ ⊢ Wrap A / com X δ , {!δ!} GlobalFiber[ p ]
    send : X ∣ p ↦ A Type
           -> Γ ⊢ ◻ X / δ GlobalFiber[ p ]
           -> Γ ⊢ Wrap A / com X δ , {!!} GlobalFiber[ p ]

    lam : Γ , A ＠ ⦗ p ⦘ ⊢ B / δ GlobalFiber[ p ] -> Γ ⊢ A ⇒ B / lam δ GlobalFiber[ p ]

  -- reduce : ∀{Δp} -> Γ ∣ p ↦ Δ , Δp Ctx -> Γ ⊢ A / δ GlobalFiber[ p ] -> Δ ⊢ A / {!!} GlobalFiber[ p ]
  -- reduce = {!!}



  _⊢_/_GlobalFibered[_] : (Γ : Ctx) -> (X : ◯Type) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ X ⟧-◯Type Com[ ⟦_⟧-◯Type ] -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)
  _⊢_/_GlobalFibered[_] Γ X δ ps = ∀ p -> p ∈ ⟨ ps ⟩ -> ∀ {A} -> X ∣ p ↦ A Type -> ∀ {Δ Δp} -> Γ ∣ p ↦ Δ , Δp Ctx -> Δ ⊢ A / {!!} GlobalFiber[ p ]

  lam-GlobalFibered : Γ , X ⊢ Y / δ GlobalFibered[ ls ] -> Γ ⊢ X ⇒ Y / lam δ GlobalFibered[ ls ]
  lam-GlobalFibered t l l∈ls {A = A ⇒ B} (X↦A ⇒ Y↦B) Γ↦Δ = lam (t l l∈ls {A = {!!}} Y↦B (Γ↦Δ , X↦A))

  -- _⊢_/_GlobalFibered[_] : (Γ : Ctx) -> (X : ◯Type) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ X ⟧-◯Type Com[ ⟦_⟧-◯Type ] -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)



  data _⇛_/_GlobalFibered[_] : (Γ Δ : Ctx) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ Δ ⟧-Ctx Com[ ⟦_⟧-◯Type ] -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)
  data _⇛_/_GlobalFibered[_] where
    ε : Γ ⇛ ε / tt GlobalFibered[ ks ]
    _,_ : Γ ⇛ Δ / δ₀ GlobalFibered[ ks ] -> Γ ⊢ X / δ₁ GlobalFibered[ ks ] -> Γ ⇛ Δ , X / δ₀ , δ₁ GlobalFibered[ ks ]

  ----------------------------------------------------------
  -- Constructing the categories
  --
  -- The local categories.
  -- Note that the Loc here is the location where the local
  -- type should be located (ergo we don't have ∨, but have
  -- an ∧ operation)
  ▲Obj : 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 _
  ▲Obj l = ∑ isLocal l



  ▲Hom : ∀ l -> ▲Obj l -> ▲Obj l -> 𝒰 _
  ▲Hom l (Γ , ΓP) (Δ , ΔP) = ∑ λ δ -> Γ ⇛ Δ / δ GlobalFibered[ l ]
    -- ∀ (Γδ : Γ ⊢Com) ->
    -- ∑ λ (ΔD : Δ ⊢Com) ->
    -- mer Γ Γδ ⇛ mer Δ ΔD ∣ ⦗ l ⦘



  -- The global category.
  -- Note that the loc here is the range of processes that
  -- participate in the choreography, thus only should contain
  -- ∨ operations).
  ◯Obj : 𝒰 _
  ◯Obj = Ctx

  ◯Hom : ◯Obj -> ◯Obj -> 𝒰 _
  ◯Hom Γ Δ = ∑ λ δ -> Γ ⇛ Δ / δ GlobalFibered[ {!!} ]
  -- ∀ (Γδ : Γ ⊢Com) ->
  --            ∑ λ (ΔD : Δ ⊢Com) ->
  --            mer Γ Γδ ⇛ mer Δ ΔD ∣ split all


  ----------------------------------------------------------
  -- Constructing the functors
  --
  -- 1) from local to global by using "＠"
  --
  ---------------------
  -- The object map
  F＠ : ▲Obj ls -> ◯Obj
  F＠ (Γ , P) = Γ
  -- F＠ l ε = ε
  -- F＠ l (Γ , A © δ) = F＠ l Γ , A ＠ l © δ


  --
  ---------------------
  -- The arrow map
  --
  map-F＠ : ∀{A B : ▲Obj ls} -> ▲Hom ls A B -> ◯Hom (F＠ A) (F＠ B)
  map-F＠ f = {!f!}
  -- We have to...
  --
  -- F＠-Var : Ξ ⊢▲-Var A -> F＠ l Ξ ⊢◯-Var A ＠ l
  -- F＠-Var zero = zero
  -- F＠-Var (suc v) = suc (F＠-Var v)

  -- F＠-Term : Ξ ⊢▲ A  -> F＠ l Ξ ⊢◯ A ＠ l
  -- F＠-Term = {!!}

  -- 2) from global to local by using ◻
  --
  ---------------------
  -- The object map
  F◻ : ∀ p -> ◯Obj -> ▲Obj p
  F◻ p ε = ε , ε
  F◻ p (Γ , X) =
    let Γ' , Γ'P = F◻ p Γ
    in (Γ' , ◻ X ＠ p) , step Γ'P

{-


  ---------------------------------------------
  -- The natural transformations
  ε-Comp : ∀(Γ : ◯Obj) -> ◯Hom (F＠ (F◻ p Γ)) Γ
  ε-Comp ε = λ Γδ → ε , ε
  ε-Comp {p = p} (Γ , X) (Γδ , Xδ & ((◻ Xα) ＠ l))
    with (Δδ , t) <- ε-Comp Γ Γδ
    = (Δδ , (Xδ ≫ com (◯mer X Xα) (re p)) & Xα) , wk-⇛ t , {!!}
    -- = (Δδ , (Xδ ≫ (com X (re p) ≫ []))) , wk-⇛ t , e
    -- where
    --   e : mer (F＠ (F◻ p Γ)) Γδ , ◻ X ＠ re p © Xδ ⊢◯ X ∣ split {{L}} all © (Xδ ≫ (com X (re p) ≫ []))
    --   e q q∈all A Ap with q ≟ p
    --   ... | no x = seq (var zero (proj-＠-≠ {!!})) (recv (var zero Ap))
    --   ... | yes refl-≡ = seq (var zero (proj-＠ {!!})) (send (var zero (proj-＠ {!!})) (var zero Ap))

  η-Comp : ∀(Γ : ▲Obj p) -> ▲Hom p Γ (F◻ p (F＠ Γ))
  η-Comp (ε , ε) = {!!}
  η-Comp {p = p} ((G , X) , step {A = A} P) = {!!}

-}

  ---------------------------------------------
  -- The products
  _×-◯_ : ◯Obj -> ◯Obj -> ◯Obj
  Γ ×-◯ ε = Γ
  Γ ×-◯ (Δ , x) = (Γ ×-◯ Δ) , x

  ---------------------------------------------
  -- The exponentials

  _⇒'-◯_ : ◯Type -> ◯Obj -> ◯Obj
  X ⇒'-◯ ε = ε
  X ⇒'-◯ (Δ , Y) = (X ⇒'-◯ Δ) , (X ⇒ Y)

  _⇒-◯_ : ◯Obj -> ◯Obj -> ◯Obj
  ε ⇒-◯ Δ = Δ
  (Γ , X) ⇒-◯ Δ = Γ ⇒-◯ (X ⇒'-◯ Δ)

  curry' : ∀{Γ x Ε} -> ◯Hom (Γ , x) Ε -> ◯Hom Γ (x ⇒'-◯ Ε)
  curry' {Ε = ε} f = tt , ε
  curry' {Ε = Ε , x} ((δ₀ , δ₁) , (f₀ , f₁)) =
    let δ₀' , f₀' = curry' (δ₀ , f₀)
    in (δ₀' , lam δ₁) , f₀' , lam-GlobalFibered f₁

  curry : ∀{Γ Δ Ε} -> ◯Hom (Γ ×-◯ Δ) Ε -> ◯Hom Γ (Δ ⇒-◯ Ε)
  curry {Δ = ε} f = f
  curry {Δ = Δ , x} f = curry (curry' f)







  ---------------------------------------------

{-


  data ▲Ann where
    ◻ : ∀{X : ◯Type} -> ◯Ann X -> ▲Ann (◻ X)
    NN : ▲Ann NN
    Unit : ▲Ann Unit
    Either : ∀{A B} -> ▲Ann A -> ▲Ann B -> ▲Ann (Either A B)
    _[_]⇒_ : ∀{A B} -> ▲Ann A -> Com -> ▲Ann B -> ▲Ann (A ⇒ B)

  data ◯Ann where
    _＠_ : ∀{A} -> ▲Ann A -> (l : 𝒫ᶠⁱⁿ (Proc L)) -> ◯Ann (A ＠ l)
    _[_]⇒_ : ∀{X Y : ◯Type} -> ◯Ann (X) -> Com -> ◯Ann (Y) -> ◯Ann (X ⇒ Y)

  ◯mer : (X : ◯Type) -> ◯Ann X -> ◯Type₊ l
  ◯mer = {!!}


  data _⊢Com : Ctx -> 𝒰 𝑖 where
    ε : ε ⊢Com
    _,_&_ : ∀{Γ} -> {X : ◯Type} -> Γ ⊢Com -> Com -> ◯Ann X -> Γ , X ⊢Com

  mer : (Γ : Ctx) -> Γ ⊢Com -> Ctx
  mer ε D = ε
  mer (Γ , X) (Γδ , Xδ & Xα) = mer Γ Γδ , ◯mer X Xα © Xδ


  -- data _⊢◯_ : Ctx -> ◯Type -> 𝒰 𝑖
  data _⊢◯-Var_©_ : Ctx -> ◯Type₊ l -> Com -> 𝒰 𝑖
  -- data _⊢_//_ : Ctx -> ▲Type -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 𝑖
  data _⇛_∣_ : Ctx -> Ctx -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)

  data Com where
    -- var : Γ ⊢◯-Var X -> Com
    com : ◯Type₊ l -> 𝒫ᶠⁱⁿ (Proc L) -> Com
    _∥_ : (δ₀ δ₁ : Com) -> Com
    _≫_ : (δ₀ δ₁ : Com) -> Com
    _⊹_ : (δ₀ δ₁ : Com) -> Com
    [] : Com


  private variable
    δ δ₀ δ₁ : Com

  -- data isLocal (l : 𝒫ᶠⁱⁿ (Proc L)) : Ctx -> 𝒰 𝑖 where
  --   ε : isLocal l ε
  --   step : isLocal l Γ -> isLocal l (Γ , A ＠ l © δ)

  data isLocal (l : 𝒫ᶠⁱⁿ (Proc L)) : Ctx -> 𝒰 𝑖 where
    ε : isLocal l ε
    step : ∀{Γ A} -> isLocal l Γ -> isLocal l (Γ , A ＠ l)


  data _⊢◯-Var_©_ where
    zero : Γ , X © δ ⊢◯-Var X © δ
    suc : Γ ⊢◯-Var X © δ₀ -> Γ , Y © δ₁  ⊢◯-Var X © δ₀


  data _∣_↦_ : ◯Type₊ l -> ⟨ Proc L ⟩ -> ▲Type₊ -> 𝒰 (𝑗) where
    proj-＠ : ∀{k} -> l ≤ re k -> A ＠ l ∣ k ↦ A
    proj-＠-≠ : ∀{k} -> (¬ l ≤ re k) -> A ＠ l ∣ k ↦ Unit


  data _⊢◯_//_©_ : (Γ : Ctx) -> ▲Type₊ -> ⟨ Proc L ⟩ -> Com -> 𝒰 (𝑗)



  _⊢◻_∣_//_ : Ctx -> ◯Type₊ l -> 𝒫ᶠⁱⁿ (Proc L) -> ⟨ Proc L ⟩ -> 𝒰 _
  _⊢◻_∣_//_ Γ X ks q = ∀ p -> p ∈ ⟨ ks ⟩ -> ∀ A -> X ∣ p ↦ A -> Γ ⊢◯ A // q © []


{-
  data _⊢◻_∣_//_ : Ctx -> ◯Type -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 𝑖 where
    [] : Γ ⊢◻ X ∣ [] // l
    _,_by_ : Γ ⊢◻ X ∣ ks // l -> X ∣ p ↦ A -> Γ ⊢◯ A // l © [] -> Γ ⊢◻ X ∣ (k ∷ ks) // l
    -}



  _⊢◯_∣_©_ : Ctx -> ◯Type₊ l -> 𝒫ᶠⁱⁿ (Proc L) -> Com -> 𝒰 _
  _⊢◯_∣_©_ Γ X ps δ = ∀ p -> p ∈ ⟨ ps ⟩ -> ∀ A -> X ∣ p ↦ A -> Γ ⊢◯ A // p © δ

{-
  data _⊢◯_∣_©_ : Ctx -> ◯Type -> 𝒫ᶠⁱⁿ (Proc L) -> Com -> 𝒰 𝑖 where
    [] : Γ ⊢◯ X ∣ [] © δ
    _,_by_ : Γ ⊢◯ X ∣ ks © δ -> X ∣ p ↦ A -> Γ ⊢◯ A // k © δ -> Γ ⊢◯ X ∣ (k ∷ ks) © δ
    -}

  data _⊢◯_//_©_ where

    var : (i : Γ ⊢◯-Var X © δ) -> X ∣ p ↦ A -> Γ ⊢◯ A // p © δ

    tt : Γ ⊢◯ Unit // p © []

    -- recv : X ∣ l ↦ A -> Γ ⊢◯ A // l © com X k
    recv : Γ , X © [] ⊢◯ A // p © δ
         -> Γ ⊢◯ A // p © (com X k ≫ δ)

    send : Γ ⊢◯ ◻ X // p © []
         -> Γ , X © [] ⊢◯ A // p © δ
         -> Γ ⊢◯ A // p © (com X (re p) ≫ δ)

    seq : Γ ⊢◯ A // p © δ₀
        -> Γ , A ＠ re p © [] ⊢◯ B // p © δ₁
        -> Γ ⊢◯ B // p © (δ₀ ≫ δ₁)

    box : ∀{X : ◯Type₊ k} -> Γ ⊢◻ X ∣ split {{L}} k // p -> Γ ⊢◯ ◻ X // p © []

    rec-Either : Γ ⊢◯ Either A B // p © []
               -> Γ , A ＠ re p © [] ⊢◯ C // p © δ₀
               -> Γ , B ＠ re p © [] ⊢◯ C // p © δ₁
               -> Γ ⊢◯ C // p © (δ₀ ⊹ δ₁)

    left : Γ ⊢◯ A // p © δ
         -> Γ ⊢◯ Either A B // p © δ

    right : Γ ⊢◯ B // p © δ
         -> Γ ⊢◯ Either A B // p © δ

    -- lam : Γ , A ⊢◯ B // k © δ -> Γ ⊢◯ A [ ]⇒


  -- data _⊢◯_/_©_ : (Γ : Ctx) -> ◯Type -> 𝒫ᶠⁱⁿ (Proc L) -> Com -> 𝒰 𝑖 where
  --   [] : Γ ⊢◯ X / ks © δ
  --   _,_by_ : Γ ⊢◯ X / ks © δ -> X ∣ p ↦ A -> Γ ⊢◯ A // k © δ -> Γ ⊢◯ X / (k ∷ ks) © δ

  infixl 23 _,_by_



  -- data _⊢_//_ where
    -- rec-Either : Γ ⊢ Either A B // l
    --            -> Γ , A ＠ l ⊢ C // l
    --            -> Γ , B ＠ l ⊢ C // l
    --            -> Γ ⊢ C // l

    -- box : Γ ⊢◻ X ∣ ks // l -> Γ ⊢ ◻ X ∣ ks // l

  -- data _⊢▲_©_ : (Γ : ▲Ctx) -> ▲Type -> Γ ⊢◯-> 𝒰 𝑖 where

  -- data _⊢▲-Var_©_ : ▲Ctx -> ▲Type -> Com -> 𝒰 𝑖 where
  --   zero : Ξ , A © δ ⊢▲-Var A © δ
  --   suc : Ξ ⊢▲-Var A © δ -> Ξ , B © δ₁ ⊢▲-Var A © δ

  data _⇛_∣_ where
    ε : Γ ⇛ ε ∣ ks
    _,_ : Γ ⇛ Δ ∣ ks -> Γ ⊢◯ X ∣ ks © δ -> Γ ⇛ Δ , X © δ ∣ ks

  wk-⇛ : Γ ⇛ Δ ∣ ks -> Γ , X © δ ⇛ Δ ∣ ks
  wk-⇛ = {!!}

{-
  embed-Term : Γ ⊢◯ X ∣ (l ∷ []) © δ -> Γ ⊢◯ X ∣ split ⊤ © δ
  embed-Term = {!!}

  embed-⇛ : Γ ⇛ Δ ∣ (l ∷ []) -> Γ ⇛ Δ ∣ split ⊤
  embed-⇛ = {!!}

-}


-}



{-





module _ where

  open import Data.Fin using (#_ ; zero ; suc ; Fin)
  open import Data.List using (_∷_ ; [])
  open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

  open import KamiTheory.Basics hiding (typed)
  open import KamiTheory.Order.Preorder.Instances

  -------------------
  -- The preorder of 3 processes with common knowledge is
  -- the standard preorder on `Fin 3 → Bool`, which inherits
  -- the structure from `Bool` itself. We encode such functions
  -- as bool-vectors of length 3. Note that while we actually
  -- have to take the opposite preorder of that, we do so implicitly
  -- by defining our singleton lists to be inverted, i.e., everywhere
  -- true except at the required position.
  PP : Preorder _
  PP = ′ StdVec 𝟚 3 ′

  -- Singletons are vectors with `true` everywhere except the required
  -- position
  singleton : Fin 3 -> ⟨ PP ⟩
  singleton i = singletonVec true false i

  -- We postulate that the relation is merely a proposition.
  postulate instance
    _ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)

  -------------------
  -- Various shorter notations
  P : 𝒰 _
  P = ⟨ PP ⟩

  -- We call the three processes `uu`, `vv` and `ww`
  uu vv ww : P
  uu = singleton (# 0)
  vv = singleton (# 1)
  ww = singleton (# 2)

  -- this is the common knowledge of both `uu` and `vv`
  uuvv : P
  uuvv = false ∷ (false ∷ (true ∷ []))

  pattern UVP = false ∷ false ∷ true ∷ []
  pattern UP = false ∷ true ∷ true ∷ []
  pattern VP = true ∷ false ∷ true ∷ []



  split-PP : ⟨ PP ⟩ → List ⟨ PP ⟩
  split-PP (x ∷ y ∷ z ∷ []) =
        pure x uu <> pure y vv <> pure z ww
    where
      pure : Bool -> ⟨ PP ⟩ -> List ⟨ PP ⟩
      pure false x = x ∷ []
      pure true x = []

  postulate instance
    _ : hasFiniteMeets PP

  open IR {Loc = PP} {{it}} split
  ----------------------------------------------------------
  -- Examples
  --
  -- 1) sending and receiving a value
  ex1 : ε , BB ＠ uu © [] ⊢◯ BB ＠ vv ∣ (uu ∷ vv ∷ []) © (com (BB ＠ vv) uu ≫ [])
  ex1 = []
      , proj-＠ refl-≤ by recv (var zero {!!})
      , proj-＠-≠ {!!} by send ((box ([] , proj-＠ refl-≤ by var zero (proj-＠ refl-≤)))) tt


  -- 2) sending and receiving a value, continuing differently depending on it
  ex2 : ε , BB ＠ uu © [] , BB ＠ vv © []
        ⊢◯
        BB ＠ uu ∣ (uu ∷ vv ∷ []) © (com (BB ＠ uuvv) uu ≫ ((com (BB ＠ uu) vv ≫ []) ⊹ []))
  ex2 = []
      , proj-＠-≠ {!!} by
        recv
        (rec-Either (var zero (proj-＠ {!!})) (send (box ([] , proj-＠ {!!} by var (suc zero) {!!})) tt) tt)

        -- (recv (proj-＠ (step ∷ (refl-≤-𝟚 ∷ (refl-≤-𝟚 ∷ [])))))
      , proj-＠ {!!} by
        send ((box ([] , proj-＠ {!!} by var zero {!!}
                       , proj-＠ {!!} by var zero {!!})))
        (rec-Either (var zero (proj-＠ {!!}))
                    (recv (var zero {!!}))
                    (left tt))



-}



