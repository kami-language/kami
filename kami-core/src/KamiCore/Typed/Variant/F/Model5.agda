
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model5 where

open import Agora.Conventions hiding (k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice

module IR {Loc : Preorder 𝑖} {{_ : hasFiniteMeets Loc}} (split : ⟨ Loc ⟩ -> List ⟨ Loc ⟩) where


  private variable
    k l : ⟨ Loc ⟩
    ks ls : List ⟨ Loc ⟩

  data ▲Type : 𝒰 𝑖
  data ◯Type : ⟨ Loc ⟩ -> 𝒰 𝑖
  data Com : 𝒰 𝑖

  -- data Comm (l : ⟨ Loc ⟩) : 𝒰 𝑖 where
  --   comm : ◯Type l -> ⟨ Loc ⟩ -> Comm l
  --   _∥_ : Comm l -> Comm l -> Comm l
  --   _≫_ : Comm l -> Comm l -> Comm l
  --   𝟘 : Comm l

  data ▲Type where
    -- the boxing operator:
    -- actually the list of locations should be the
    -- partition of `l`.
    ◻ : ◯Type l -> ▲Type
    NN : ▲Type
    Unit : ▲Type
    Either : ▲Type -> ▲Type -> ▲Type
    -- _[_]⇒_ : ▲Type -> 

  pattern BB = Either Unit Unit

  -- infix 40 ◻_∣_

  data ◯Type where
    _＠_ : ▲Type -> (l : ⟨ Loc ⟩) -> ◯Type l
    _⇒_ : ◯Type l -> ◯Type l -> ◯Type l

  infix 30 _＠_
  infix 45 _⇒_

  data ◯Ctx : 𝒰 𝑖 where
    ε : ◯Ctx
    _,_©_ : ◯Ctx -> ◯Type l -> Com -> ◯Ctx

  infixl 30 _,_©_

  -- 𝓁 : ◯Ctx -> ℕ
  -- 𝓁 ε = 0
  -- 𝓁 (Γ , x) = suc (𝓁 Γ)

  data ▲Ctx : 𝒰 𝑖 where
    ε : ▲Ctx
    _,_©_ : ▲Ctx -> ▲Type -> Com -> ▲Ctx

  private variable
    Γ Δ : ◯Ctx
    X Y Z : ◯Type l
    Ξ : ▲Ctx
    A B C D : ▲Type



  -- data _⊢◯_ : ◯Ctx -> ◯Type l -> 𝒰 𝑖
  data _⊢◯-Var_©_ : ◯Ctx -> ◯Type l -> Com -> 𝒰 𝑖
  -- data _⊢_//_ : ◯Ctx -> ▲Type -> ⟨ Loc ⟩ -> 𝒰 𝑖
  data _⇛_∣_ : ◯Ctx -> ◯Ctx -> List ⟨ Loc ⟩ -> 𝒰 𝑖

  data Com where
    -- var : Γ ⊢◯-Var X -> Com
    com : ◯Type l -> ⟨ Loc ⟩ -> Com
    _∥_ : (δ₀ δ₁ : Com) -> Com
    _≫_ : (δ₀ δ₁ : Com) -> Com
    _⊹_ : (δ₀ δ₁ : Com) -> Com
    [] : Com
    -- app : Γ , X ⊢◯-Com -> 

  -- _[_]-Com : suc Com -> Com -> Com
  -- _[_]-Com = {!!}

  private variable
    δ δ₀ δ₁ : Com

  data isLocal (l : ⟨ Loc ⟩) : ◯Ctx -> 𝒰 𝑖 where
    ε : isLocal l ε
    step : isLocal l Γ -> isLocal l (Γ , A ＠ l © δ)

  -- _⊢_ : ◯Ctx -> ◯Type l -> 𝒰 𝑖
  -- _⊢_ Γ A = Γ ⊢[ 𝟘 ] A

  data _⊢◯-Var_©_ where
    zero : Γ , X © δ ⊢◯-Var X © δ
    suc : Γ ⊢◯-Var X © δ₀ -> Γ , Y © δ₁  ⊢◯-Var X © δ₀

{-
  data _⊢◯_ where
    broadcast : Γ ⊢◯ ◻ X ∣ ks ＠ l -> Γ ⊢◯ X
    lam : Γ , X ⊢◯ Y -> Γ ⊢◯ X ⇒ Y
    app : Γ ⊢◯ X ⇒ Y -> Γ ⊢◯ X -> Γ ⊢◯ Y
    -- seq : Γ ⊢ X -> Γ , X ⊢ Y -> Γ ⊢ Y

-}

  data _∣_↦_ : ◯Type l -> ⟨ Loc ⟩ -> ▲Type -> 𝒰 𝑖 where
    proj-＠ : l ≤ k -> A ＠ l ∣ k ↦ A
    proj-＠-≠ : (¬ k ∼ l) -> A ＠ k ∣ l ↦ Unit



  data _⊢◯_//_©_ : (Γ : ◯Ctx) -> ▲Type -> ⟨ Loc ⟩ -> Com -> 𝒰 𝑖

  data _⊢◻_∣_//_ : ◯Ctx -> ◯Type l -> List ⟨ Loc ⟩ -> ⟨ Loc ⟩ -> 𝒰 𝑖 where
    [] : Γ ⊢◻ X ∣ [] // l
    _,_by_ : Γ ⊢◻ X ∣ ks // l -> X ∣ k ↦ A -> Γ ⊢◯ A // l © [] -> Γ ⊢◻ X ∣ (k ∷ ks) // l

  data _⊢◯_∣_©_ : ◯Ctx -> ◯Type l -> List ⟨ Loc ⟩ -> Com -> 𝒰 𝑖 where
    [] : Γ ⊢◯ X ∣ [] © δ
    _,_by_ : Γ ⊢◯ X ∣ ks © δ -> X ∣ k ↦ A -> Γ ⊢◯ A // k © δ -> Γ ⊢◯ X ∣ (k ∷ ks) © δ

  data _⊢◯_//_©_ where

    var : (i : Γ ⊢◯-Var X © δ) -> X ∣ k ↦ A -> Γ ⊢◯ A // k © δ

    tt : Γ ⊢◯ Unit // k © []

    -- recv : X ∣ l ↦ A -> Γ ⊢◯ A // l © com X k
    recv : Γ , X © [] ⊢◯ A // l © δ
         -> Γ ⊢◯ A // l © (com X k ≫ δ)

    send : Γ ⊢◯ ◻ X // k © []
         -> Γ , X © [] ⊢◯ A // k © δ
         -> Γ ⊢◯ A // k © (com X k ≫ δ)

    seq : Γ ⊢◯ A // k © δ₀
        -> Γ , A ＠ k © [] ⊢◯ B // k © δ₁
        -> Γ ⊢◯ B // k © (δ₀ ≫ δ₁)

    box : ∀{X : ◯Type k} -> Γ ⊢◻ X ∣ split k // l -> Γ ⊢◯ ◻ X // l © []

    rec-Either : Γ ⊢◯ Either A B // l © []
               -> Γ , A ＠ l © [] ⊢◯ C // l © δ₀
               -> Γ , B ＠ l © [] ⊢◯ C // l © δ₁
               -> Γ ⊢◯ C // l © (δ₀ ⊹ δ₁)

    left : Γ ⊢◯ A // k © δ
         -> Γ ⊢◯ Either A B // k © δ

    right : Γ ⊢◯ B // k © δ
         -> Γ ⊢◯ Either A B // k © δ

    -- lam : Γ , A ⊢◯ B // k © δ -> Γ ⊢◯ A [ ]⇒


  -- data _⊢◯_/_©_ : (Γ : ◯Ctx) -> ◯Type l -> List ⟨ Loc ⟩ -> Com -> 𝒰 𝑖 where
  --   [] : Γ ⊢◯ X / ks © δ
  --   _,_by_ : Γ ⊢◯ X / ks © δ -> X ∣ k ↦ A -> Γ ⊢◯ A // k © δ -> Γ ⊢◯ X / (k ∷ ks) © δ

  infixl 23 _,_by_



  -- data _⊢_//_ where
    -- rec-Either : Γ ⊢ Either A B // l
    --            -> Γ , A ＠ l ⊢ C // l
    --            -> Γ , B ＠ l ⊢ C // l
    --            -> Γ ⊢ C // l

    -- box : Γ ⊢◻ X ∣ ks // l -> Γ ⊢ ◻ X ∣ ks // l

  -- data _⊢▲_©_ : (Γ : ▲Ctx) -> ▲Type -> Γ ⊢◯-> 𝒰 𝑖 where

  data _⊢▲-Var_©_ : ▲Ctx -> ▲Type -> Com -> 𝒰 𝑖 where
    zero : Ξ , A © δ ⊢▲-Var A © δ
    suc : Ξ ⊢▲-Var A © δ -> Ξ , B © δ₁ ⊢▲-Var A © δ

  data _⇛_∣_ where
    ε : Γ ⇛ ε ∣ ks
    _,_ : Γ ⇛ Δ ∣ ks -> Γ ⊢◯ X ∣ ks © δ  -> Γ ⇛ Δ , X © δ ∣ ks

  embed-Term : Γ ⊢◯ X ∣ (l ∷ []) © δ -> Γ ⊢◯ X ∣ split ⊤ © δ
  embed-Term = {!!}

  embed-⇛ : Γ ⇛ Δ ∣ (l ∷ []) -> Γ ⇛ Δ ∣ split ⊤
  embed-⇛ = {!!}


  ----------------------------------------------------------
  -- Constructing the categories
  --
  -- The local categories.
  -- Note that the Loc here is the location where the local
  -- type should be located (ergo we don't have ∨, but have
  -- an ∧ operation)
  ▲Obj : ⟨ Loc ⟩ -> 𝒰 𝑖
  ▲Obj l = ∑ isLocal l

  ▲Hom : ∀ l -> ▲Obj l -> ▲Obj l -> 𝒰 _
  ▲Hom l (Γ , ΓP) (Δ , ΔP) = Γ ⇛ Δ ∣ (l ∷ [])


  -- The global category.
  -- Note that the loc here is the range of processes that
  -- participate in the choreography, thus only should contain
  -- ∨ operations).
  ◯Obj : 𝒰 𝑖
  ◯Obj = ◯Ctx

  ◯Hom : ◯Obj -> ◯Obj -> 𝒰 _
  ◯Hom Γ Δ = Γ ⇛ Δ ∣ split ⊤

  ----------------------------------------------------------
  -- Constructing the functors
  --
  -- 1) from local to global by using "＠"
  --
  ---------------------
  -- The object map
  F＠ : ▲Obj l -> ◯Obj
  F＠ (Γ , P) = Γ
  -- F＠ l ε = ε
  -- F＠ l (Γ , A © δ) = F＠ l Γ , A ＠ l © δ

  --
  ---------------------
  -- The arrow map
  --
  map-F＠ : ∀{A B : ▲Obj l} -> ▲Hom l A B -> ◯Hom (F＠ A) (F＠ B)
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
  F◻ : ∀ l -> ◯Obj -> ▲Obj l
  F◻ l ε = ε , ε
  F◻ l (Γ , X © δ) =
    let Γ' , Γ'P = F◻ l Γ
    in (Γ' , ◻ X ＠ l © δ) , step Γ'P

  ---------------------------------------------
  -- The natural transformations
  ε-Comp : ∀(Γ : ◯Obj) -> ◯Hom (F＠ (F◻ l Γ)) Γ
  ε-Comp ε = ε
  ε-Comp {l = l} (Γ , X © δ) = {!!} , e
    where
      e : ∀ {Γ} -> Γ , ◻ X ＠ l © δ ⊢◯ X ∣ split ⊤ © δ
      e = {!!}






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



  split : ⟨ PP ⟩ → List ⟨ PP ⟩
  split (x ∷ y ∷ z ∷ []) =
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






