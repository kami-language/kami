
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Model7 where

open import Agora.Conventions hiding (k ; m ; _∣_ ; _⊔_ ; ls)
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
open isProcessSet {{...}} public using (hasDecidableEquality:Proc)




module _ {A : 𝒰 𝑖} where
  data isPrefix : List A -> List A -> 𝒰 𝑖 where
    done : ∀{xs} -> isPrefix [] xs
    step : ∀{a as bs} -> isPrefix as bs -> isPrefix (a ∷ as) (a ∷ bs)



-- module _ (I : 𝒰 𝑖) where
data ComType : 𝒰₀ where
  Com : ComType
  Unit : ComType
  _××_ : ComType -> ComType -> ComType
  _⇒_ : ComType -> ComType -> ComType

infixr 30 _××_ _⇒_

{-
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
-}



-- module IR {Loc : Preorder 𝑖} {{_ : hasFiniteMeets Loc}} (split : 𝒫ᶠⁱⁿ (Proc L) -> 𝒫ᶠⁱⁿ (Proc L)) where
-- module IR {Loc : Preorder 𝑖} {{L : isProcessSet 𝑗}} where
module IR {{L : isProcessSet 𝑗}} where

  private variable
    -- k l : 𝒫ᶠⁱⁿ (Proc L)
    ps qs ks ls : 𝒫ᶠⁱⁿ (Proc L)
    p q k l : ⟨ Proc L ⟩
    is js : List ⟨ Proc L ⟩

  data Mode : 𝒰₀ where
    ◯ ▲ : Mode

  data Type : Mode -> 𝒰 𝑗
  data isClosed : ∀{m} -> Type m -> 𝒰 𝑗

  -- data ▲Type : 𝒰 (𝑗)
  -- data ▲Type : 𝒰 (𝑗)
  -- data ◯Type : 𝒰 (𝑗)
  -- data ◯Type : 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)
  -- data Com : 𝒰 𝑖

  -- data ▲Ann : ▲Type -> 𝒰 𝑖
  -- data ◯Ann : ◯Type -> 𝒰 𝑖


  ▲Type : 𝒰 _
  ▲Type = Type ▲

  ◯Type : 𝒰 _
  ◯Type = Type ◯


  data Type where
    ◻ : Type ◯ -> Type ▲
    [_∣_]◅_ : Type ◯ -> (𝒫ᶠⁱⁿ (Proc L)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc L)) -> Type ▲ -> Type ▲
    NN : ∀{m} -> Type m
    Unit : ∀{m} -> Type m
    Either : ∀{m} -> Type m -> Type m -> Type m
    _⇒_ : ∀{m} -> Type m -> Type m -> Type m
    _××_ : ∀{m} -> Type m -> Type m -> Type m
    Tr : ∀{m} -> Type m -> Type m
    _＠_ : Type ▲ -> (l : 𝒫ᶠⁱⁿ (Proc L)) -> Type ◯

  private variable
    m : Mode
    X Y Z : ◯Type
    A B C D : ▲Type
    T S U : Type m
    T₀ T₁ S₀ S₁ : Type m

  data isClosed where
    ◻ : isClosed X -> isClosed (◻ X)
    -- [_∣_]◅_ : Type ◯ -> (𝒫ᶠⁱⁿ (Proc L)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc L)) -> Type ▲ -> Type ▲
    NN : isClosed {m} NN
    Unit : isClosed {m} Unit
    Either : isClosed T -> isClosed S -> isClosed (Either T S)
    _⇒_ : isClosed T -> isClosed S -> isClosed (_⇒_ T S)
    _××_ : isClosed T -> isClosed S -> isClosed (_××_ T S)
    Tr : isClosed T -> isClosed (Tr T)
    _＠_ : isClosed A -> (l : 𝒫ᶠⁱⁿ (Proc L)) -> isClosed (A ＠ l)

  pattern BB = Either Unit Unit

  infix 30 _＠_

  -- pl : ∀{m} -> Type m -> Type plain
  -- pl = {!!}



  data Ctx : 𝒰 (𝑗) where
    ε : Ctx
    _,[_] : Ctx -> 𝒫ᶠⁱⁿ (Proc L) -> Ctx
    _,_ : Ctx -> ◯Type -> Ctx


  data isLocal (l : 𝒫ᶠⁱⁿ (Proc L)) : Ctx -> 𝒰 (𝑗) where
    ε : isLocal l ε
    step : ∀{Γ A} -> isLocal l Γ -> isLocal l (Γ , A ＠ l)


  -- ⟦_⟧-Type : ◯Type -> ComType
  -- ⟦_⟧-Type : ∀{m} -> Type m -> ComType
  -- PlType : Type plain -> ComType
  -- PlType = ⟦_⟧-Type

  private variable
    -- Ξ : ▲Ctx
    Γ Δ : Ctx
    x y z : ComType
    -- A₊ B₊ C₊ D₊ : ▲Type
    -- c d : x ⊢ ℂ Com[ PlType ]


  ---------------------------------------------

  -- data _∣_↦_Type : ∀{m} -> Type m -> ⟨ Proc L ⟩ -> ▲Type -> 𝒰 (𝑗) where
  --   proj-＠ : p ∈ ⟨ ps ⟩ -> A ＠ ps ∣ ⦗ p ⦘ ∷ [] ↦ A Type
  --   proj-＠-≠ : (¬ p ∈ ⟨ ps ⟩) -> A ＠ ps ∣ ⦗ p ⦘ ∷ [] ↦ Unit Type
  --   _⇒_ : X ∣ ⦗ p ⦘ ∷ [] ↦ A Type -> Y ∣ ⦗ p ⦘ ∷ [] ↦ B Type -> (X ⇒ Y) ∣ ⦗ p ⦘ ∷ [] ↦ (A ⇒ B) Type

  --   proj-◻ : X ∣ ⦗ p ⦘ ∷ [] ↦ A Type -> ◻ X ∣ ⦗ p ⦘ ∷ [] ↦ [ X ]◅ A Type


  mutual
    data π_∣_↦_Type : Type ◯ -> ((𝒫ᶠⁱⁿ (Proc L)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc L))) -> Type ▲ -> 𝒰 (𝑗) where
      proj-＠ : ∀{ps pps qs A B} -> ps ≤ qs -> ω A ∣ pps ↦ B Type -> π A ＠ qs ∣ ps , pps ↦ B Type
      proj-＠-≠ : ∀{ps pps qs A} -> (¬ ps ≤ qs) -> π A ＠ qs ∣ ps , pps ↦ Unit Type
      _⇒_ : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (X ⇒ Y) ∣ p , ps ↦ (A ⇒ B) Type
      _××_ : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (X ×× Y) ∣ p , ps ↦ (A ×× B) Type
      Either : ∀{p ps A B} -> π X ∣ p , ps ↦ A Type -> π Y ∣ p , ps ↦ B Type -> π (Either X Y) ∣ p , ps ↦ Either A B Type
      Tr : ∀{p ps A } -> π X ∣ p , ps ↦ A Type -> π (Tr X) ∣ p , ps ↦ Tr A Type
      Unit : ∀{p ps} -> π Unit ∣ p , ps ↦ Unit Type

    data ω_∣_↦_Type : Type ▲ -> List (𝒫ᶠⁱⁿ (Proc L)) -> Type ▲ -> 𝒰 (𝑗) where
      done : ∀{A} -> ω A ∣ [] ↦ A Type
      proj-◻ : ∀{p ps A} -> π X ∣ p , ps ↦ A Type -> ω ◻ X ∣ p ∷ ps ↦ [ X ∣ p , ps ]◅ A Type
      -- proj-[] : ∀{p ps qs} -> isPrefix ps qs -> ω A ∣ qs ↦ B Type -> ω ([ X ∣ p , ps ]◅ A) ∣ p ∷ qs ↦ [ X ∣ p , qs ]◅ B Type
      Unit-▲ : ∀{p ps} -> ω Unit ∣ p ∷ ps ↦ Unit Type


  mutual
    π-Type : (X : ◯Type) -> isClosed X -> ((𝒫ᶠⁱⁿ (Proc L)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc L))) -> Type ▲
    π-Type Unit Unit ps = Unit
    π-Type NN NN ps = NN
    π-Type (Either X Y) (Either Xp Yp) ps = Either (π-Type X Xp ps) (π-Type Y Yp ps)
    π-Type (X ⇒ Y) (Xp ⇒ Yp) ps = π-Type X Xp ps ⇒ π-Type Y Yp ps
    π-Type (X ×× Y) (Xp ×× Yp) ps = π-Type X Xp ps ×× π-Type Y Yp ps
    π-Type (Tr X) (Tr Xp) ps = Tr (π-Type X Xp ps)
    π-Type (A ＠ l) (Ap ＠ l) (p , ps) with decide-≤ p l
    ... | no x = Unit
    ... | yes x = ω-Type A Ap ps

    ω-Type : (A : ▲Type) -> isClosed A -> List (𝒫ᶠⁱⁿ (Proc L)) -> Type ▲
    ω-Type A Ap [] = A
    ω-Type (◻ X) (◻ Xp) (p ∷ ps) = [ X ∣ p , ps ]◅ π-Type X Xp (p , ps)
    ω-Type NN NN (p ∷ ps) = {!!}
    ω-Type Unit Unit (p ∷ ps) = {!!}
    ω-Type (Either T S) (Either x x₁) (x₂ ∷ x₃) = {!!}
    ω-Type (T ⇒ S) (x ⇒ x₁) (x₂ ∷ x₃) = {!!}
    ω-Type (T ×× S) (x ×× x₁) (x₂ ∷ x₃) = {!!}
    ω-Type (Tr T) (Tr x) (x₁ ∷ x₂) = {!!}


  data ϕ_↦_ : ∀{m} -> Type m -> Type m -> 𝒰 𝑗 where
    proj-◻ : ∀{p ps} -> ϕ [ X ∣ p , ps ]◅ A ↦ ◻ X
    proj-＠ : ∀{p ps} -> ϕ [ X ∣ p , ps ]◅ A ↦ A
    _⇒_ : ϕ T₀ ↦ T₁ -> ϕ S₀ ↦ S₁ -> ϕ (T₀ ⇒ S₀) ↦ (T₁ ⇒ S₁)

  id-ϕ : ∀{X : Type m} -> ϕ X ↦ X
  id-ϕ = {!!}


  -- mutual
  --   π-Type-Proof : (X : Type ◯) -> (ps : (𝒫ᶠⁱⁿ (Proc L)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc L))) -> π X ∣ ps ↦ π-Type X ps Type
  --   π-Type-Proof Unit ps = Unit
  --   π-Type-Proof (Either X Y) ps = Either (π-Type-Proof X ps) (π-Type-Proof Y ps)
  --   π-Type-Proof (X ⇒ Y) ps = π-Type-Proof X ps ⇒ π-Type-Proof Y ps
  --   π-Type-Proof (Tr X) ps = Tr (π-Type-Proof X ps)
  --   π-Type-Proof (A ＠ l) (p , ps) with decide-≤ p l
  --   ... | no x = proj-＠-≠ x
  --   ... | yes x = proj-＠ x (ω-Type-Proof A ps)

  --   ω-Type-Proof : (A : Type ▲) -> (ps : List (𝒫ᶠⁱⁿ (Proc L))) -> ω A ∣ ps ↦ ω-Type A ps Type
  --   ω-Type-Proof = {!!}



  data _∣_↦_Ctx : Ctx -> (l : List (𝒫ᶠⁱⁿ (Proc L))) -> Ctx -> 𝒰 (𝑗) where
    ε : ∀{p} -> ε ∣ ⦗ p ⦘ ∷ [] ↦ ε Ctx
    _,_ : ∀{p ps} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> π X ∣ p , [] ↦ A Type -> Γ , X ∣ p ∷ ps ↦ (Δ , A ＠ p) Ctx
    stepRes : ∀{p ps} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> Γ ,[ p ] ∣ ps ↦ Δ ,[ p ] Ctx


  π-Ctx : Ctx -> List (𝒫ᶠⁱⁿ (Proc L)) -> Ctx
  π-Ctx = {!!}

  π-Ctx-Proof : (Γ : Ctx) -> (i : List (𝒫ᶠⁱⁿ (Proc L))) -> Γ ∣ i ↦ π-Ctx Γ i Ctx
  π-Ctx-Proof = {!!}


  ----------------------------------------------------------
  -- Com terms

  ↓_ : Type m -> ComType
  ↓ ◻ T = ↓ T
  ↓ ([ T ∣ x ]◅ T₁) = {!!}
  ↓ NN = Unit
  ↓ Unit = Unit
  ↓ Either T T₁ = {!!}
  ↓ (T ⇒ S) = ↓ T ⇒ ↓ S
  ↓ (T ×× S) = ↓ T ×× ↓ S
  ↓ Tr T = Com ×× ↓ T
  ↓ (T ＠ l) = ↓ T

  infix 50 ↓_

  data _⊢Var_GlobalFiber[_] : (Γ : Ctx) -> (A : ▲Type) -> (𝒫ᶠⁱⁿ (Proc L)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc L)) -> 𝒰 (𝑗) where
    zero : ∀{ps} -> π X ∣ ps ↦ A Type -> ϕ A ↦ B -> Γ , X ⊢Var B GlobalFiber[ ps ]
    suc : ∀{ps} -> Γ ⊢Var A GlobalFiber[ ps ] -> Γ , X ⊢Var A GlobalFiber[ ps ]
    res : ∀{p p' ps} -> Γ ⊢Var A GlobalFiber[ p , (p' ∷ ps) ] -> Γ ,[ p ] ⊢Var A GlobalFiber[ p' , ps ]

  data _⊢Var_Global : Ctx -> Type ◯ -> 𝒰 𝑗 where
    zero : ∀{Γ A} -> Γ , A ⊢Var A Global
    suc : ∀{Γ A B} -> Γ ⊢Var A Global -> (Γ , B) ⊢Var A Global


  data _⊢_Com : Ctx -> ComType -> 𝒰 𝑗 where
    var : ∀{Γ A p} -> Γ ⊢Var A GlobalFiber[ ⦗ p ⦘ , [] ] -> Γ ⊢ ↓ A Com
    extern : ∀{Γ A p} -> Γ ,[ p ] ⊢ A Com -> Γ ⊢ A Com

    -- _＠_ : Γ ⊢ A Com -> (l : 𝒫ᶠⁱⁿ (Proc L)) -> Γ ⊢ A ＠ l Com
    -- unbox : Γ ⊢ ◻ X Com -> Γ ⊢ X Com

    _,_ : ∀{Γ A B} -> Γ ⊢ A Com -> Γ ⊢ B Com -> Γ ⊢ A ×× B Com
    -- lam◯ : ∀{Γ A B} -> (Γ , A) ⊢ B Com -> Γ ⊢ A ⇒ B Com
    lam : ∀{Γ X B} -> (Γ , X) ⊢ B Com -> Γ ⊢ ↓ X ⇒ B Com
    app : ∀{Γ} {A B} -> Γ ⊢ A ⇒ B Com -> Γ ⊢ A Com -> Γ ⊢ B Com
    tt : ∀{Γ} -> Γ ⊢ Unit Com

    com : ∀{Γ} (p : ⟨ Proc L ⟩) (T : Type ◯) -> Γ ⊢ Com Com
    -- com : ∀{Γ} (T : Type ◯) -> Γ ⊢ T Com -> Γ ⊢ S Com -> Γ ⊢ Tr S Com
    -- _≫_ : ∀{Γ} -> Γ ⊢ Tr S Com -> Γ ⊢ Tr S Com -> Γ ⊢ Tr S Com
    -- 𝟘 : ∀{Γ} -> Γ ⊢ Tr T Com

    -- _⊹_ : ∀{Γ} -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ Com -> Γ ⊢ ℂ Com

  private variable
    c d : ComType
    δ δ₀ δ₁ : Γ ⊢ c Com

  wk-Com : Γ ⊢ c Com -> Γ , X ⊢ c Com
  wk-Com = {!!}

  -- data _∣_↦_Com : ∀{Γ Δ} -> Γ ∣ ⦗ p ⦘ ∷ [] ↦ Δ , Δp Ctx -> X ∣ ⦗ p ⦘ ∷ [] ↦ A Type -> 𝒰 (𝑗) where

  -- data _∣_↦_Com : ∀{Γ Δ} -> Γ ⊢ X Com -> ⟨ Proc L ⟩ -> Δ ⊢ A Com -> 𝒰 (𝑗) where
  --   proj-＠ : p ∈ ⟨ ps ⟩ -> δ ＠ ps ∣ p ↦ δ Com

  π-Com : ∀{p} -> π X ∣ p , [] ↦ A Type -> Γ ⊢ ↓ X Com -> Γ ⊢ ↓ A Com
  π-Com = {!!}


  π-Com2 : ∀{p} -> Γ ∣ p ∷ [] ↦ Δ Ctx -> Γ ⊢ c Com -> Δ ⊢ c Com
  π-Com2 Γp (var x) = {!!}
  π-Com2 Γp (extern t) = {!!}
  π-Com2 Γp (t , t₁) = {!!}
  π-Com2 Γp (lam t) = lam (π-Com2 (Γp , {!!}) t)
  π-Com2 Γp (app t t₁) = {!!}
  π-Com2 Γp tt = {!!}
  π-Com2 Γp (com p T) = {!!}

  v1-Com : ∀ X -> Γ , X ⊢ ↓ X Com
  v1-Com NN = {!!}
  v1-Com Unit = {!!}
  v1-Com (Either X X₁) = {!!}
  v1-Com (X ⇒ X₁) = {!!}
  v1-Com (X ×× Y) = {!!}
  v1-Com (Tr X) = {!!}
  v1-Com (X ＠ l) = var (zero (proj-＠ {!!} done) {!!})


  π-Com' : ∀{p} -> Γ ∣ p ∷ [] ↦ Δ Ctx -> π X ∣ p , [] ↦ A Type -> Γ ⊢ ↓ X Com -> Δ ⊢ ↓ A Com
  π-Com' {X = Unit} {Unit} Γp Unit t = tt
  π-Com' {X = Either X X₁} {A} Γp Xp t = {!!}
  π-Com' {X = X ⇒ X₁} {.(_ ⇒ _)} Γp (Xp ⇒ Xp₁) t = lam (π-Com' (Γp , Xp) Xp₁ (app (wk-Com t) {!!}))
  π-Com' {X = X ×× X₁} {.(_ ×× _)} Γp (Xp ×× Xp₁) t = {!!}
  π-Com' {X = Tr X} {A} Γp Xp t = {!!}
  π-Com' {X = X ＠ l} {.X} Γp (proj-＠ x done) t = {!!}
  π-Com' {X = X ＠ l} {.Unit} Γp (proj-＠-≠ x) t = tt





  ----------------------------------------------------------
  -- Old


  -- data _⊢_/_Global : (Γ : Ctx) -> (X : ◯Type) -> Γ ⊢ X Com -> 𝒰 (𝑗) where

{-
    lam : Γ , X ⊢ Y / δ Global -> Γ ⊢ X ⇒ Y / (lam δ) Global

    app : Γ ⊢ X ⇒ Y / (δ₀) Global
        -> Γ ⊢ X / δ₁ Global
        -> Γ ⊢ Y / app δ₀ δ₁ Global

   -- seq : Γ ⊢ X / (c , δ₀) Global
    --     -> Γ , X ⊢ Y / δ₁ Global
    --     -> Γ ⊢ Y / c ≫-↷ (app (lam δ₁) (𝟘 , δ₀)) Global

    -- left : Γ ⊢ X / δ₀ Global
    --      -> Γ ⊢ Either X Y / (δ₀ , δ₁) Global


    -- either : Γ ⊢ Either X Y / (δ₀ , δ₁) Global
    --          -> Γ , X ⊢ Z / ζ₀ Global
    --          -> Γ , Y ⊢ Z / ζ₁ Global
    --          -> Γ ⊢ Z / (app (lam ζ₀) δ₀ ⊹-Com app (lam ζ₁) δ₁) Global

-}



  record _⊢_/_GlobalFibered[_] (Γ : Ctx) (X : ◯Type) (δ : Γ ⊢ ↓ X Com) (ps : 𝒫ᶠⁱⁿ (Proc L)) : 𝒰 (𝑗)

  data _⊢_/_GlobalFiber[_] : (Γ : Ctx) -> (A : ▲Type) -> Γ ⊢ ↓ A Com -> ⟨ Proc L ⟩ -> 𝒰 (𝑗) where
    var : ∀{p} -> (v : Γ ⊢Var A GlobalFiber[ ⦗ p ⦘ , [] ]) -> Γ ⊢ A / var v GlobalFiber[ p ]

    recv : π X ∣ ⦗ p ⦘ , [] ↦ A Type -> Γ ⊢ Tr A / com q X , δ GlobalFiber[ p ]

    send : (v : π X ∣ ⦗ p ⦘ , [] ↦ A Type)
           -- -> unbox δ₀ ∣ p ↦ δ₁ Com
           -> Γ ⊢ ◻ X / δ₀ GlobalFiber[ p ]
           -> Γ ⊢ Tr A / com p X , π-Com v δ₀ GlobalFiber[ p ]

    extern : Γ ,[ ⦗ q ⦘ ] ⊢ A / δ GlobalFiber[ p ] -> Γ ⊢ A / extern δ GlobalFiber[ p ]

    lam : Γ , A ＠ ⦗ p ⦘ ⊢ B / δ GlobalFiber[ p ] -> Γ ⊢ A ⇒ B / lam δ GlobalFiber[ p ]
    app : Γ ⊢ A ⇒ B / δ₀ GlobalFiber[ p ] -> Γ ⊢ A / δ₁ GlobalFiber[ p ] -> Γ ⊢ B / app δ₀ δ₁ GlobalFiber[ p ]

    tt : Γ ⊢ Unit / tt GlobalFiber[ p ]

    box : p ∈ ⟨ qs ⟩ -> Γ ,[ qs ] ⊢ X / δ GlobalFibered[ ps ]
          -> Γ ⊢ ◻ X / extern δ GlobalFiber[ p ]

    -- box' : Γ ,[ ⦗ p ⦘ ] ⊢ X / δ GlobalFibered[ ps ]
    --       -> Γ ⊢ ◻ X / {!!} GlobalFiber[ p ]

    -- box-close : ∀{p ps δ} -> Γ ⊢ [ X ∣ p , ps ]◅ A / δ GlobalFiber[ q ] -> Γ ⊢ ◻ X / {!!} GlobalFiber[ q ]


  record _⊢_/_GlobalFibered[_] Γ X δ ps where
    inductive ; constructor incl
    field ⟨_⟩ : ∀ p -> p ∈ ⟨ ps ⟩ -> ∀ {A} -> (Xp : π X ∣ ⦗ p ⦘ , [] ↦ A Type)
                -> ∀ {Δ} -> (Γp : Γ ∣ ⦗ p ⦘ ∷ [] ↦ Δ Ctx)
                -- -> ∑ λ δ' -> δ ∣ p ↦ δ' Com ×-𝒰
                -> Δ ⊢ A / π-Com' Γp Xp δ GlobalFiber[ p ]

  open _⊢_/_GlobalFibered[_] public

{-
-}



  lam-GlobalFibered : Γ , X ⊢ Y / δ GlobalFibered[ ps ] -> Γ ⊢ X ⇒ Y / lam δ GlobalFibered[ ps ]
  lam-GlobalFibered t = incl λ {p p∈ps (X↦A ⇒ Y↦B) Γ↦Δ -> {!!} } -- lam (⟨ t ⟩ p p∈ps Y↦B (Γ↦Δ , X↦A)) }
    -- let δ' , _ , t' = (⟨ t ⟩ p p∈ps Y↦B (Γ↦Δ , X↦A))
    -- in lam▲ δ' , {!!} , lam t' }


{-
  app-GlobalFibered : Γ ⊢ X ⇒ Y / δ₀ GlobalFibered[ ps ]
                   -> Γ ⊢ X / δ₁ GlobalFibered[ ps ]
                   -> Γ ⊢ Y / app δ₀ δ₁ GlobalFibered[ ps ]
  ⟨ app-GlobalFibered {X = X} t s ⟩ p p∈ps Y↦Y' Γ↦Δ =
    let X' = π-Type X (⦗ p ⦘ ∷ [])
        X↦X' = π-Type-Proof X (⦗ p ⦘ ∷ [])
        δt , _ , t' = (⟨ t ⟩ p p∈ps (X↦X' ⇒ Y↦Y') Γ↦Δ)
        δs , _ , s' = (⟨ s ⟩ p p∈ps X↦X' Γ↦Δ)
    in app δt δs , {!!} , app t' s'


  letin-GlobalFibered : Γ ⊢ X / δ₁ GlobalFibered[ ps ]
                     -> Γ , X ⊢ Y / δ₀ GlobalFibered[ ps ]
                     -> Γ ⊢ Y / app (lam◯ δ₀) δ₁ GlobalFibered[ ps ]
  letin-GlobalFibered t s = app-GlobalFibered (lam-GlobalFibered s) t


  mutual
    lem-13' : ∀{ps qs} -> C ∣ ps ↦ A Type -> C ∣ ps <> qs ↦ B Type -> A ∣ ps <> qs ↦ B Type
    lem-13' {ps = x ∷ ps} (proj-◻ v) (proj-◻ w) =  let z = lem-13 v w in proj-[] {!!} z
    lem-13' {ps = x ∷ ps} (proj-[] x₁ x₂) (proj-[] x₃ x₄) = proj-[] {!!} (lem-13' x₂ x₄)
    lem-13' {ps = []} Unit-▲ x = x
    lem-13' {ps = x ∷ ps} Unit-▲ Unit-▲ = Unit-▲
    lem-13' done w = w

    lem-13 : ∀{p ps qs} -> X ∣ p ∷ ps ↦ A Type -> X ∣ p ∷ ps <> qs ↦ B Type -> A ∣ ps <> qs ↦ B Type
    lem-13 (proj-＠ x v) (proj-＠ x₁ w) = lem-13' v w
    lem-13 (proj-＠ x v) (proj-＠-≠ x₁) = ⊥-elim (x₁ x)
    lem-13 (proj-＠-≠ x) (proj-＠ x₁ w) = ⊥-elim (x x₁)
    lem-13 (proj-＠-≠ x) (proj-＠-≠ x₁) = Unit-▲
    lem-13 (v ⇒ v₁) (w ⇒ w₁) = {!!}
    lem-13 Unit-◯ Unit-◯ = Unit-▲

  lem-12 : ∀{p ps qs} -> X ∣ p ∷ ps ↦ A Type -> X ∣ p ∷ ps <> qs ↦ B Type -> (A ＠ p) ∣ p ∷ ps <> qs ↦ B Type
  lem-12 v w = proj-＠ refl-≤ (lem-13 v w)

  -- projVar : ∀{ps qs} -> Γ ∣ ps ↦ Δ Ctx -> Γ ⊢Var A GlobalFiber[ qs ] -> Δ ⊢Var A GlobalFiber[ qs ]
  -- projVar (p , v) (zero w) = zero (lem-11 v w)
  -- projVar (p , x) (suc v) = suc (projVar p v)
  -- projVar (stepRes p) (res v) = res (projVar p v)

  projVar1 : ∀{ps qs} -> Γ ∣ ps ↦ Δ Ctx -> Γ ⊢Var A GlobalFiber[ ps <> qs ] -> Δ ⊢Var A GlobalFiber[ ps <> qs ]
  projVar1 (p , v) (zero w) = zero (lem-12 v w )
  projVar1 (p , x) (suc v) = suc (projVar1 p v)
  projVar1 (stepRes p) (res v) = res (projVar1 p v)

  projVar3 : ∀{p qs} -> Γ ∣ p ∷ [] ↦ Δ Ctx -> Γ ,[ p ] ⊢Var A GlobalFiber[ qs ] -> Δ ,[ p ] ⊢Var A GlobalFiber[ qs ]
  projVar3 p (res v) with projVar1 p (v)
  ... | (w) = res w

  map-Var : (∀{qs A} -> Γ ⊢Var A GlobalFiber[ qs ] -> Δ ⊢Var A GlobalFiber[ qs ]) -> Γ ⊢ X / δ GlobalFibered[ ps ] -> Δ ⊢ X / {!!} GlobalFibered[ ps ]
  map-Var = {!!}


  resVar : ∀{qs rs ps ps'} -> rs ≤ qs -> Γ ⊢Var A GlobalFiber[ ps <> (qs ∷ ps') ] -> Γ ⊢Var A GlobalFiber[ ps <> (rs ∷ ps') ]
  resVar p (zero x) = zero {!!}
  resVar p (suc v) = suc (resVar p v)
  resVar {ps = ps} rel (res {p = p} v) = res (resVar {ps = p ∷ ps} rel v)

  transRes-GlobalFibered : ∀{qs rs δ} -> rs ≤ qs -> Γ ,[ qs ] ⊢ X / δ GlobalFibered[ ps ] -> Γ ,[ rs ] ⊢ X / {!!} GlobalFibered[ ps ]
  transRes-GlobalFibered = {!!}



  box-GlobalFibered : Γ ,[ qs ] ⊢ X / δ GlobalFibered[ ps ]
                     -> Γ ⊢ ◻ X ＠ qs / {!!} GlobalFibered[ ps ]
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠ x done) Γ↦Δ =
    let t' = transRes-GlobalFibered x t
    in {!!} , {!!} , box' {p = p} (map-Var (projVar3 (Γ↦Δ)) t')
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠-≠ x) Γ↦Δ = {!!} , {!!} , tt



  -- map-local-project-var : ∀{ps p} -> A ∣ ps ↦ B Type -> Γ ⊢Var B GlobalFiber[ p ] -> Γ ⊢Var A GlobalFiber[ p ]

  -- map-local-project-var : ∀{ps p} -> A ∣ ps ↦ B Type -> Γ ⊢Var B GlobalFiber[ p ] -> Γ ⊢Var A GlobalFiber[ p ]
  -- map-local-project-var q (zero x) = zero {!!}
  -- map-local-project-var q (suc v) = {!!}
  -- map-local-project-var q (res v) = res (map-local-project-var q v)

  map-local-project : ∀{ps p} -> A ∣ ps ↦ B Type -> Γ ⊢ B / δ GlobalFiber[ p ] -> Γ ⊢ A / {!!} GlobalFiber[ p ]
  map-local-project = {!!}
  -- -- map-local-project = {!!}
  -- map-local-project (proj-◻ q) t = {!!}
  -- map-local-project (proj-[] x q) t = let t' = map-local-project q {!!} in {!!}
  -- map-local-project done t = t
  -- map-local-project Unit-▲ t = t
  {-
  -}


  -- showing that the ◻ modality commutes with exponentials
  -- Γ ⊢ ◻ A ⇒ ◻ B -> Γ ⊢ ◻ (A ⇒ B)
  -- Γ . ◻ X .{ ◻ } ⊢ Y ... ◻μ ⇒ ◻η  should split to   id ⋆ (μ ⇒ η),
  -- Γ .{ ◻ } . X ⊢ Y
  -- and in fact, every map ◻ ⇒ ◻ should be the identity. ◻ ⇒ ◻ ⨾ ＠ i ⨾ ◻ ⇒ 

  commute-◻-Exp : ∀{δ} -> Γ ⊢ (◻ X ⇒ ◻ Y) / δ GlobalFiber[ p ] -> Γ ⊢ ◻ (X ⇒ Y) / {!!} GlobalFiber[ p ]
  commute-◻-Exp {Γ} {X} {Y} {p} {δ} t = {!!}

  -- showing that the ＠ modality commutes with exponentials
  commute-＠-Exp : ∀ ps -> ∀{δ} -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) / δ GlobalFibered[ qs ] -> Γ ⊢ (A ⇒ B) ＠ ps / {!!} GlobalFibered[ qs ]
  ⟨ commute-＠-Exp ps t ⟩ q q∈qs (proj-＠ q∈ps done) Γp =
    let δ' , _ , t' = (⟨ t ⟩ q q∈qs (proj-＠ q∈ps done ⇒ proj-＠ q∈ps done) Γp)
    in δ' , {!!} , t'
  ⟨ commute-＠-Exp ps t ⟩ q q∈qs (proj-＠-≠ x) Γp = tt , {!!} , tt


{-
  commute⁻¹-＠-Exp : ∀ ps -> ∀{δ} -> Γ ⊢ (A ⇒ B) ＠ ps / δ GlobalFibered[ qs ] -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) / {!!} GlobalFibered[ qs ]
  commute⁻¹-＠-Exp = {!!}


-}



  -- with q ∈? ⟨ ps ⟩
  -- ... | no x = {!!}
  -- ... | yes x = {!!}


    -- incl λ {l l∈ls Xp Γ↦Δ ->
    -- let δ' , _ , t' = (⟨ t ⟩ l l∈ls {!!} {!!})
    -- in {!!}
    -- }



{-
  -- _⊢_/_GlobalFibered[_] : (Γ : Ctx) -> (X : ◯Type) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ X ⟧-Type Com[ PlType ] -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)



  data _⇛_/_GlobalFibered[_] : (Γ Δ : Ctx) -> ⟦ Γ ⟧-Ctx ⊢ ⟦ Δ ⟧-Ctx Com[ PlType ] -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)
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

  ◯mer : (X : ◯Type) -> ◯Ann X -> ◯Type l
  ◯mer = {!!}


  data _⊢Com : Ctx -> 𝒰 𝑖 where
    ε : ε ⊢Com
    _,_&_ : ∀{Γ} -> {X : ◯Type} -> Γ ⊢Com -> Com -> ◯Ann X -> Γ , X ⊢Com

  mer : (Γ : Ctx) -> Γ ⊢Com -> Ctx
  mer ε D = ε
  mer (Γ , X) (Γδ , Xδ & Xα) = mer Γ Γδ , ◯mer X Xα © Xδ


  -- data _⊢◯_ : Ctx -> ◯Type -> 𝒰 𝑖
  data _⊢◯-Var_©_ : Ctx -> ◯Type l -> Com -> 𝒰 𝑖
  -- data _⊢_//_ : Ctx -> ▲Type -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 𝑖
  data _⇛_∣_ : Ctx -> Ctx -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 (𝑗)

  data Com where
    -- var : Γ ⊢◯-Var X -> Com
    com : ◯Type l -> 𝒫ᶠⁱⁿ (Proc L) -> Com
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


  data _∣_↦_ : ◯Type l -> ⟨ Proc L ⟩ -> ▲Type -> 𝒰 (𝑗) where
    proj-＠ : ∀{k} -> l ≤ re k -> A ＠ l ∣ k ↦ A
    proj-＠-≠ : ∀{k} -> (¬ l ≤ re k) -> A ＠ l ∣ k ↦ Unit


  data _⊢◯_//_©_ : (Γ : Ctx) -> ▲Type -> ⟨ Proc L ⟩ -> Com -> 𝒰 (𝑗)



  _⊢◻_∣_//_ : Ctx -> ◯Type l -> 𝒫ᶠⁱⁿ (Proc L) -> ⟨ Proc L ⟩ -> 𝒰 _
  _⊢◻_∣_//_ Γ X ks q = ∀ p -> p ∈ ⟨ ks ⟩ -> ∀ A -> X ∣ ⦗ p ⦘ ∷ [] ↦ A -> Γ ⊢◯ A // q © []


{-
  data _⊢◻_∣_//_ : Ctx -> ◯Type -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒫ᶠⁱⁿ (Proc L) -> 𝒰 𝑖 where
    [] : Γ ⊢◻ X ∣ [] // l
    _,_by_ : Γ ⊢◻ X ∣ ks // l -> X ∣ ⦗ p ⦘ ∷ [] ↦ A -> Γ ⊢◯ A // l © [] -> Γ ⊢◻ X ∣ (k ∷ ks) // l
    -}



  _⊢◯_∣_©_ : Ctx -> ◯Type l -> 𝒫ᶠⁱⁿ (Proc L) -> Com -> 𝒰 _
  _⊢◯_∣_©_ Γ X ps δ = ∀ p -> p ∈ ⟨ ps ⟩ -> ∀ A -> X ∣ ⦗ p ⦘ ∷ [] ↦ A -> Γ ⊢◯ A // p © δ

{-
  data _⊢◯_∣_©_ : Ctx -> ◯Type -> 𝒫ᶠⁱⁿ (Proc L) -> Com -> 𝒰 𝑖 where
    [] : Γ ⊢◯ X ∣ [] © δ
    _,_by_ : Γ ⊢◯ X ∣ ks © δ -> X ∣ ⦗ p ⦘ ∷ [] ↦ A -> Γ ⊢◯ A // k © δ -> Γ ⊢◯ X ∣ (k ∷ ks) © δ
    -}

  data _⊢◯_//_©_ where

    var : (i : Γ ⊢◯-Var X © δ) -> X ∣ ⦗ p ⦘ ∷ [] ↦ A -> Γ ⊢◯ A // p © δ

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

    box : ∀{X : ◯Type k} -> Γ ⊢◻ X ∣ split {{L}} k // p -> Γ ⊢◯ ◻ X // p © []

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
  --   _,_by_ : Γ ⊢◯ X / ks © δ -> X ∣ ⦗ p ⦘ ∷ [] ↦ A -> Γ ⊢◯ A // k © δ -> Γ ⊢◯ X / (k ∷ ks) © δ

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

-}
-}
