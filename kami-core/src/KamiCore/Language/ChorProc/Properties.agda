

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Properties where

open import Data.List using (drop)

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

open import KamiTheory.Basics hiding (_⋆_)
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.UniqueSortedList.NonEmpty
open import KamiTheory.Data.UniqueSortedList.Properties
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorProc.Definition




module Chor𝔓roc/Properties (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]

  --------------------------------------------------------------
  -- Operations on Types and contexts
  --------------------------------------------------------------

  -------------------
  -- Types

  F-Type : (a ⟶ b) -> ⊢Type ⟦ a ⟧-Mode -> ⊢Type ⟦ b ⟧-Mode
  F-Type id' x = x
  F-Type (`＠` U ⨾ μ) x = F-Type μ (x ＠ U)
  F-Type (`[]` ⨾ μ) x = F-Type μ (◻ x)

  F-Type-map : ∀{X : ⊢Type ⟦ a ⟧-Mode} {μ : a ⟶ b} {ν : b ⟶ c} -> F-Type (μ ◆ ν) X ≡ F-Type ν (F-Type μ X)
  F-Type-map {μ = id'} = refl-≡
  F-Type-map {μ = `＠` U ⨾ μ} = F-Type-map {μ = μ}
  F-Type-map {μ = `[]` ⨾ μ} = F-Type-map {μ = μ}

  -------------------
  -- Contexts

  TargetCtx : ProcMode -> 𝒰 _
  TargetCtx ▲ = ⊢Ctx × ⟨ P ⟩
  TargetCtx ◯ = ⊢Ctx

  addRestr : (μ : a ⟶ b) -> TargetCtx ⟦ b ⟧-Mode -> TargetCtx ⟦ a ⟧-Mode
  addRestr id' Γ = Γ
  addRestr (`＠` U ⨾ μ) Γ = addRestr μ Γ , U
  addRestr (`[]` ⨾ μ) Γ = let Γ' , U = addRestr μ Γ in Γ' ,[ U ]


  forget : TargetCtx ⟦ a ⟧-Mode -> ⊢Ctx
  forget {a = ◯} Γ = Γ
  forget {a = ▲ x} Γ = fst Γ

  cong-Ctx,Var : {A B : ⊢Type ◯} -> A ≡ B -> _≡_ {A = ⊢Ctx} (Γ , A) (Γ , B)
  cong-Ctx,Var refl-≡ = refl-≡

  transp-Ctx-Var : ∀{ps} -> (Γ ≡ Δ) -> Γ ⊢Var A GlobalFiber[ ps ] -> Δ ⊢Var A GlobalFiber[ ps ]
  transp-Ctx-Var refl-≡ t = t

  --------------------------------------------------------------
  -- Proofs on Operations on Types and contexts
  --------------------------------------------------------------


  eval-F-type-right : F-Type (ν ◆' `＠` V ⨾ id') X ≡ (F-Type ν X) ＠ V
  eval-F-type-right {V = V} {ν = ν}  = F-Type-map {μ = ν} {ν = `＠` V ⨾ id'}



  --------------------------------------------------------------
  -- Types and context projections
  --------------------------------------------------------------

  mutual
    π-Type : (X : ⊢Type ◯) -> ((𝒫₊ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This))) -> ⊢Type ▲
    π-Type Unit ps = Unit
    π-Type (Either X Y) ps = Either (π-Type X ps) (π-Type Y ps)
    π-Type (X ⇒ Y) ps = π-Type X ps ⇒ π-Type Y ps
    π-Type (X ×× Y)  ps = π-Type X ps ×× π-Type Y ps
    π-Type (Tr X)  ps = Tr (π-Type X ps)
    π-Type (Lst X)  ps = Lst (π-Type X ps)
    π-Type (A ＠ l) (p , ps) with decide-≤ p l
    ... | no x = Unit
    ... | yes x = ω-Type A ps


    ω-Type : (A : ⊢Type ▲) -> List (𝒫₊ᶠⁱⁿ (Proc This)) -> ⊢Type ▲
    ω-Type A [] = A
    -- ω-Type (◻ X) (p ∷ ps) = [ X ∣ p , ps ]◅ π-Type X (p , ps)
    ω-Type (◻ X) (p ∷ ps) = π-Type X (p , ps)
    ω-Type Unit (p ∷ ps) = Unit
    -- ω-Type (Either T S)  (p ∷ ps) = Unit
    -- ω-Type (T ⇒ S) (p ∷ ps) = Unit
    -- ω-Type (T ×× S) (p ∷ ps) = Unit
    -- ω-Type (Tr T) (p ∷ ps) = Unit
    -- ω-Type (Lst T) (p ∷ ps) = Unit
    ω-Type (Either T S)  (p ∷ ps) = Either (ω-Type T (p ∷ ps)) (ω-Type S (p ∷ ps))
    ω-Type (T ⇒ S) (p ∷ ps) = _⇒_ (ω-Type T (p ∷ ps)) (ω-Type S (p ∷ ps))
    ω-Type (T ×× S) (p ∷ ps) = _××_ (ω-Type T (p ∷ ps)) (ω-Type S (p ∷ ps))
    ω-Type (Tr T) (p ∷ ps) = Tr (ω-Type T (p ∷ ps))
    ω-Type (Lst T) (p ∷ ps) = Lst (ω-Type T (p ∷ ps))

  π-Type-Proof : (X : ⊢Type ◯) -> (ps : (𝒫₊ᶠⁱⁿ (Proc This))) -> π X ∣ ps , [] ↦ (π-Type X (ps , [])) Type
  π-Type-Proof Unit ps = Unit
  π-Type-Proof (Either X Y) ps = Either (π-Type-Proof X ps) (π-Type-Proof Y ps)
  π-Type-Proof (X ⇒ Y) ps = π-Type-Proof X ps ⇒ π-Type-Proof Y ps
  π-Type-Proof (Tr X) ps = Tr (π-Type-Proof X ps)
  π-Type-Proof (Lst X) ps = Lst (π-Type-Proof X ps)
  π-Type-Proof (A ＠ l) p with decide-≤ p l
  ... | no x = proj-＠-≠ x
  ... | yes x = proj-＠ x done
  π-Type-Proof (X ×× Y) ps = _××_ (π-Type-Proof X ps) (π-Type-Proof Y ps)

  eval-π-＠ : π-Type (A ＠ ps) (ps , []) ≡ A
  eval-π-＠ {A = A} {ps = ps} with decide-≤ ps ps
  ... | yes X = refl-≡
  ... | no X = ⊥-elim ({!!})

{-
  mutual
    π-Type-Proof : (X : ⊢Type ◯) -> (ps : (𝒫₊ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫₊ᶠⁱⁿ (Proc This))) -> π X ∣ ps ↦ π-Type X ps Type
    π-Type-Proof Unit ps = Unit
    π-Type-Proof (Either X Y) ps = Either (π-Type-Proof X ps) (π-Type-Proof Y ps)
    π-Type-Proof (X ⇒ Y) ps = π-Type-Proof X ps ⇒ π-Type-Proof Y ps
    π-Type-Proof (Tr X) ps = Tr (π-Type-Proof X ps)
    π-Type-Proof (Lst X) ps = Lst (π-Type-Proof X ps)
    π-Type-Proof (A ＠ l) (p , ps) with decide-≤ p l
    ... | no x = proj-＠-≠ x
    ... | yes x = proj-＠ x (ω-Type-Proof A ps)
    π-Type-Proof (X ×× Y) ps = _××_ (π-Type-Proof X ps) (π-Type-Proof Y ps)

    ω-Type-Proof : (A : ⊢Type ▲) -> (ps : List (𝒫₊ᶠⁱⁿ (Proc This))) -> ω A ∣ ps ↦ ω-Type A ps Type
    ω-Type-Proof A [] = done
    ω-Type-Proof (◻ X) (p ∷ ps) = proj-◻ (π-Type-Proof X (p , ps))
    ω-Type-Proof Unit (p ∷ ps) = Unit
    ω-Type-Proof (Either T S)  (p ∷ ps) = {!!}
    ω-Type-Proof (T ⇒ S) (p ∷ ps) = {!!}
    ω-Type-Proof (T ×× S) (p ∷ ps) = ω-Type-Proof T (p ∷ ps) ×× ω-Type-Proof S (p ∷ ps)
    ω-Type-Proof (Tr T) (p ∷ ps) = {!!}
    ω-Type-Proof (Lst T) (p ∷ ps) = {!!}

-}

  π-Ctx : ⊢Ctx -> List (𝒫₊ᶠⁱⁿ (Proc This)) -> ⊢Ctx
  π-Ctx Γ [] = Γ
  π-Ctx ε (i ∷ is) = ε
  π-Ctx (Γ ,[ x ]) (i ∷ is) = π-Ctx Γ (x ∷ i ∷ is) ,[ x ]
  π-Ctx (Γ , x) (i ∷ is) = π-Ctx Γ (i ∷ is) , π-Type x (i , []) ＠ i

  local-Proof : ∀ {Γ Δ p ps} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> isLocal p Δ
  local-Proof ε = ε
  local-Proof (p , x) = (local-Proof p) , _
  local-Proof (stepRes p) = stepRes (local-Proof p)

  π-Ctx-Proof : (Γ : ⊢Ctx) -> (i : List (𝒫₊ᶠⁱⁿ (Proc This))) -> Γ ∣ i ↦ π-Ctx Γ i Ctx
  π-Ctx-Proof Γ [] = done
  π-Ctx-Proof ε (i ∷ is) = ε
  π-Ctx-Proof (Γ ,[ x ]) (i ∷ is) = stepRes (π-Ctx-Proof Γ (x ∷ i ∷ is)) 
  π-Ctx-Proof (Γ , x) (i ∷ is) = π-Ctx-Proof Γ (i ∷ is) , π-Type-Proof x i


  data _≡-Local_ {ps} : {Γ Δ : ⊢Ctx} (Γp : isLocal ps Γ) (Δp : isLocal ps Δ) -> 𝒰 𝑗 where
    refl-Local : ∀{Γ} {Γp : isLocal ps Γ} -> Γp ≡-Local Γp

  map-,Local : {Γ Δ : ⊢Ctx} (Γp : isLocal ps Γ) (Δp : isLocal ps Δ)
             -> Γp ≡-Local Δp -> A ≡ B -> Γp , A ≡-Local Δp , B
  map-,Local _ _ refl-Local refl-≡ = refl-Local

  map-stepRes : {Γ Δ : ⊢Ctx} (Γp : isLocal ps Γ) (Δp : isLocal ps Δ)
             -> Γp ≡-Local Δp -> ∀{q} -> stepRes {k = q} Γp ≡-Local stepRes {k = q} Δp
  map-stepRes _ _ refl-Local = refl-Local



  idempotent-local : ∀{Δ : ⊢Ctx} -> ∀{pps} -> (Δp : isLocal ps Δ) -> local-Proof (π-Ctx-Proof Δ (ps ∷ pps)) ≡-Local Δp
  idempotent-local ε = refl-Local
  idempotent-local {ps = ps} (Δp , A) = map-,Local _ _ (idempotent-local Δp) (eval-π-＠ {ps = ps})
  idempotent-local (stepRes Δp) = map-stepRes _ _ (idempotent-local Δp)

  idempotent-local' : ∀{Δ Δₗ : ⊢Ctx} -> ∀{pps} -> (Δp : isLocal ps Δ) -> Δ ∣ (ps ∷ pps) ↦ Δₗ Ctx -> Δ ≡ Δₗ

  idempotent-local' ε ε = refl-≡
  idempotent-local' (Δp , A) (P₁ , proj-＠ x done) = cong₂-≡ _,_ (idempotent-local' Δp P₁) refl-≡
  idempotent-local' (Δp , A) (P₁ , proj-＠-≠ x) = {!!} -- ⊥-elim (x refl-≤)
  idempotent-local' (stepRes Δp) (stepRes P₁) = cong-≡ (_,[ _ ]) (idempotent-local' Δp P₁)







  unique-π : ∀{X A B ps} -> π X ∣ ps , [] ↦ A Type -> π X ∣ ps , [] ↦ B Type -> A ≡ B
  unique-π (proj-＠ x done) (proj-＠ x₂ done) = refl-≡
  unique-π (proj-＠ x done) (proj-＠-≠ x₂) = {!!} -- ⊥-elim (x₂ x)
  unique-π (proj-＠-≠ x) (proj-＠ x₁ done) = {!!} -- ⊥-elim (x x₁)
  unique-π (proj-＠-≠ x) (proj-＠-≠ x₁) = refl-≡
  unique-π (p ⇒ p₁) (q ⇒ q₁) = cong₂-≡ _⇒_ (unique-π p q) (unique-π p₁ q₁)
  unique-π (p ×× p₁) (q ×× q₁) = cong₂-≡ _××_ (unique-π p q) (unique-π p₁ q₁)
  unique-π (Either p p₁) (Either q q₁) = cong₂-≡ Either (unique-π p q) (unique-π p₁ q₁)
  unique-π (Tr p) (Tr q) = cong-≡ Tr (unique-π p q)
  unique-π (Lst p) (Lst q) = cong-≡ Lst (unique-π p q)
  unique-π Unit Unit = refl-≡

  unique-π-Ctx : ∀{Γ Δ₀ Δ₁ p ps qs} -> Γ ∣ p ∷ ps ↦ Δ₀ Ctx -> Γ ∣ p ∷ qs ↦ Δ₁ Ctx -> Δ₀ ≡ Δ₁
  unique-π-Ctx ε ε = refl-≡
  unique-π-Ctx (P₁ , x) (Q , x₁) with unique-π x x₁
  ... | refl-≡ = cong-≡ (_, _) (unique-π-Ctx P₁ Q)
  unique-π-Ctx (stepRes P₁) (stepRes Q) = cong-≡ (_,[ _ ]) (unique-π-Ctx P₁ Q)

  unique-π-Ctx-≤ : ∀{Γ Δ₀ Δ₁ p ps q qs} -> q ≤ p -> Γ ∣ p ∷ ps ↦ Δ₀ Ctx -> Γ ∣ q ∷ qs ↦ Δ₁ Ctx -> Δ₀ ∣ q ∷ [] ↦ Δ₁ Ctx
  unique-π-Ctx-≤ pp ε ε = ε
  unique-π-Ctx-≤ pp (P₁ , x) (Q , x₁) = {!!} , {!!}
  unique-π-Ctx-≤ pp (stepRes P₁) (stepRes Q) = {!!}



  -- unique-ω : ∀{X A B ps} -> ω X ∣ ps ↦ A Type -> ω X ∣ ps ↦ B Type -> A ≡ B
  -- unique-ω = {!!}

  -- unique-π : ∀{X A B ps} -> π X ∣ ps ↦ A Type -> π X ∣ ps ↦ B Type -> A ≡ B

{-
  split-π : ∀{p ps} -> π X ∣ p , ps ↦ A Type -> ω π-Type X (p , []) ∣ ps ↦ A Type
  split-π {p = p} (proj-＠ {qs = qs} x x₁) with decide-≤ p qs
  ... | no x₂ = ⊥-elim (x₂ x)
  ... | yes x₂ = x₁
  split-π {p = p} (proj-＠-≠ {qs = qs} x) with decide-≤ p qs
  split-π {p = p} {[]} (proj-＠-≠ {qs = _} x) | no x₂ = done
  split-π {p = p} {x₁ ∷ ps} (proj-＠-≠ {qs = _} x) | no x₂ = Unit
  ... | yes x₂ = ⊥-elim (x x₂)
  -- with p ≟ ⊥
  -- split-π {p = p} (proj-＠-≠ {qs = _} (no x)) | yes x₂ | no P = ⊥-elim (x x₂)
  -- split-π {p = p} (proj-＠-≠ {qs = _} (yes x)) | yes x₂ | no P = ⊥-elim (P x)
  -- -- 
  -- split-π {p = p} {[]} (proj-＠-≠ {qs = _} (no x)) | yes x₂ | yes P = done
  -- split-π {p = p} {x₁ ∷ ps} (proj-＠-≠ {qs = _} (no x)) | yes x₂ | yes P = Unit
  -- split-π {p = p} {[]} (proj-＠-≠ {qs = _} (yes x)) | yes x₂ | yes P = done
  -- split-π {p = p} {x₁ ∷ ps} (proj-＠-≠ {qs = _} (yes x)) | yes x₂ | yes P = Unit
  split-π {ps = []} (P ⇒ P₁) = {!!}
  -- split-π {ps = x ∷ ps} (P ⇒ P₁) = split-π P ⇒ split-π P₁
  split-π (P ×× P₁) = {!!}
  split-π (Either P P₁) = {!!}
  split-π (Tr P) = {!!}
  split-π (Lst P) = {!!}
  split-π Unit = {!!}
  -}


  --------------------------------------------------------------
  -- Properties of variables
  --------------------------------------------------------------

{-
  mutual
    lem-13' : ∀{ps qs} -> ω C ∣ ps ↦ A Type -> ω C ∣ ps <> qs ↦ B Type -> ω A ∣ ps <> qs ↦ B Type
    lem-13' {ps} {.ps} done Q = Q
    lem-13' {.(◻ _)} (proj-◻ x) (proj-◻ x₁) = {!proj-◻ ?!} --  -- (lem-13 x x₁)
    lem-13' {.Unit} {.Unit} Unit Q = {!!}
    -- lem-13' {ps = x ∷ ps} (proj-◻ v) (proj-◻ w) =  ? -- let z = lem-13 v w in proj-[] {!!} z
    -- -- lem-13' {ps = x ∷ ps} (proj-◻ x₁ x₂) (proj-◻ x₃ x₄) = proj-[] {!!} (lem-13' x₂ x₄)
    -- lem-13' {ps = []} Unit x = x
    -- lem-13' {ps = x ∷ ps} Unit Unit = Unit
    -- lem-13' done w = w

    lem-13 : ∀{p ps qs} -> π X ∣ p , ps ↦ A Type -> π X ∣ p , ps <> qs ↦ B Type -> ω A ∣ ps <> qs ↦ B Type
    lem-13 (proj-＠ x x₁) (proj-＠ x₂ x₃) = {!!} -- lem-13' x₁ x₃
    lem-13 (proj-＠ x x₁) (proj-＠-≠ x₂) = {!!}
    lem-13 (proj-＠-≠ x) (proj-＠ x₁ x₂) = {!!}
    lem-13 (proj-＠-≠ x) (proj-＠-≠ x₁) = {!!}
    lem-13 (P₁ ⇒ P₂) (Q ⇒ Q₁) = {!!}
    lem-13 (P₁ ×× P₂) (Q ×× Q₁) = {!!}
    lem-13 (Either P₁ P₂) (Either Q Q₁) = {!!}
    lem-13 (Tr P₁) (Tr Q) = {!!}
    lem-13 (Lst P₁) (Lst Q) = {!!}
    lem-13 Unit Unit = {!!}
-}

  lem-14 : ∀{p ps} -> π X ∣ p , [] ↦ A Type -> π X ∣ p , ps ↦ B Type -> ω A ∣ ps ↦ B Type
  lem-14 (proj-＠ x done) (proj-＠ x₂ x₃) = x₃
  lem-14 (proj-＠ x done) (proj-＠-≠ x₂) = {!!} -- ⊥-elim (x₂ x)
  lem-14 (proj-＠-≠ x) (proj-＠ x₂ x₃) = {!!} -- ⊥-elim (x x₂)
  lem-14 {ps = []} (proj-＠-≠ x) (proj-＠-≠ x₁) = done
  lem-14 {ps = _ ∷ _} (proj-＠-≠ x) (proj-＠-≠ x₁) = Unit
  lem-14 (v ⇒ v₁) (w ⇒ w₁) with unique-π v w | unique-π v₁ w₁
  ... | refl-≡ | refl-≡ = done
  lem-14 (v ×× v₁) (w ×× w₁) with unique-π v w | unique-π v₁ w₁
  ... | refl-≡ | refl-≡ = done
  lem-14 (Either v v₁) (Either w w₁) with unique-π v w | unique-π v₁ w₁
  ... | refl-≡ | refl-≡ = done
  lem-14 (Tr v) (Tr w) with unique-π v w
  ... | refl-≡ = done
  lem-14 (Lst v) (Lst w) with unique-π v w
  ... | refl-≡ = done
  lem-14 Unit Unit = done


  lem-12 : ∀{p ps} -> π X ∣ p , [] ↦ A Type -> π X ∣ p , ps ↦ B Type -> π (A ＠ p) ∣ p , ps ↦ B Type
  lem-12 v w = proj-＠ {!!} (lem-14 v w)



  lem-12-α : ∀{p ps} -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> α X ∣ ⦗ p ⦘₊ , ps ↦ B Type -> α (A ＠ ⦗ p ⦘₊) ∣ ⦗ p ⦘₊ , ps ↦ B Type
  lem-12-α (proj-＠ x₂ x₃) (proj-＠ x x₁) = {!!}
  lem-12-α (proj-＠-≠ x₂) (proj-＠ x x₁) = {!!}
  lem-12-α (proj-＠ x₁ x₂) (proj-＠-≠ x) = {!⊥-elim (x x₁)!}
  lem-12-α (proj-＠-≠ x₁) (proj-＠-≠ x) = {!proj-＠ ? ?!}



  projVar1 : ∀{ps qs} -> Γ ∣ ps ↦ Δ Ctx -> Γ ⊢Var A GlobalFiber[ ps <> qs ] -> Δ ⊢Var A GlobalFiber[ ps <> qs ]
  projVar1 done v = v
  projVar1 (p , v) (none) = none
  -- projVar1 (p , v) (zero x w) = zero x (lem-12 v w )
  projVar1 (p , v) (zero x w) = zero x {!!} -- (lem-12 v w )
  projVar1 (p , x) (suc v) = suc (projVar1 p v)
  projVar1 (stepRes p) (res v) = res (projVar1 p v)

  projVar3 : ∀{p qs} -> Γ ∣ p ∷ [] ↦ Δ Ctx -> Γ ,[ p ] ⊢Var A GlobalFiber[ qs ] -> Δ ,[ p ] ⊢Var A GlobalFiber[ qs ]
  projVar3 p (res v) with projVar1 p (v)
  ... | (w) = res w



  --------------------------------------------------------------
  -- Generic term constructions of the ChorProc calculus
  --------------------------------------------------------------
  --
  commute⁻¹-＠-Exp : ∀ ps -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) GlobalFibered[ qs ] -> Γ ⊢ (A ⇒ B) ＠ ps GlobalFibered[ qs ]
  ⟨ commute⁻¹-＠-Exp ps t ⟩ q q∈qs (proj-＠ q∈ps done) Γp =
    let t' = (⟨ t ⟩ q q∈qs (proj-＠ q∈ps done ⇒ proj-＠ q∈ps done) Γp)
    in t'
  ⟨ commute⁻¹-＠-Exp ps t ⟩ q q∈qs (proj-＠-≠ x) Γp = tt


  commute-＠-Exp : ∀ ps -> Γ ⊢ (A ⇒ B) ＠ ps GlobalFibered[ qs ]
                        -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) GlobalFibered[ qs ]
  ⟨ commute-＠-Exp ps t ⟩ p x (proj-＠ x₁ done ⇒ proj-＠ x₃ done) Γp = ⟨ t ⟩ _ x (proj-＠ x₁ done) Γp
  ⟨ commute-＠-Exp ps t ⟩ p x (proj-＠ x₁ done ⇒ proj-＠-≠ x₃) Γp = {!!} -- ⊥-elim (x₃ x₁)
  ⟨ commute-＠-Exp ps t ⟩ p x (proj-＠-≠ x₁ ⇒ proj-＠ x₂ done) Γp = {!!} -- ⊥-elim (x₁ x₂)
  ⟨ commute-＠-Exp ps t ⟩ p x (proj-＠-≠ x₁ ⇒ proj-＠-≠ x₂) Γp = lam tt

  map-Var-Fiber : ∀ {p} -> isLocal ⦗ p ⦘₊ Δ -> isLocal ⦗ p ⦘₊ Γ -> (∀{A qs} -> Γ ⊢Var A GlobalFiber[ ⦗ p ⦘₊ ∷ qs ] -> Δ ⊢Var A GlobalFiber[ ⦗ p ⦘₊ ∷ qs ]) -> Γ ⊢ B GlobalFiber[ p ] -> Δ ⊢ B GlobalFiber[ p  ]

  map-Var : (∀{q A Γₗ Δₗ qs} -> q ∈ ⟨ fst ps ⟩ -> Γ ∣ (⦗ q ⦘₊ ∷ []) ↦ Γₗ Ctx -> Δ ∣ (⦗ q ⦘₊ ∷ []) ↦ Δₗ Ctx -> Γₗ ⊢Var A GlobalFiber[ ⦗ q ⦘₊ ∷ qs ] -> Δₗ ⊢Var A GlobalFiber[ ⦗ q ⦘₊ ∷ qs ])
            -> Γ ⊢ X GlobalFibered[ ps ] -> Δ ⊢ X GlobalFibered[ ps ]

  map-Var-Fiber Δp Γp V (var v) = var (V v)
  map-Var-Fiber Δp Γp V (recv x) = recv x
  map-Var-Fiber Δp Γp V (send v t) = send v (map-Var-Fiber Δp Γp V t)
  map-Var-Fiber Δp Γp V (box' x) = box' (map-Var (λ {q∈ps (stepRes Γproj) (stepRes Δproj) (res v) → res (transp-Ctx-Var ((idempotent-local' Δp Δproj)) (V (transp-Ctx-Var (sym-≡ (idempotent-local' Γp Γproj)) v)))}) x) -- (map-Var (λ {(res v) -> res (V v)}) x)
  map-Var-Fiber Δp Γp V (pure t) = pure (map-Var-Fiber Δp Γp V t)
  map-Var-Fiber Δp Γp V (seq t s) =
    let t' = map-Var-Fiber Δp Γp V t
        s' = map-Var-Fiber (Δp , _) (Γp , _) (λ {(suc v) -> suc (V v)
                              ; none -> none
                              ; (zero v w) -> (zero v w)}) s
    in seq t' s'
  map-Var-Fiber Δp Γp V (lam t) =
    let t' = map-Var-Fiber (Δp , _) (Γp , _) (λ {(suc v) -> suc (V v)
                              ; none -> none
                              ; (zero v w) -> (zero v w)}) t
    in lam t'
  map-Var-Fiber Δp Γp V (app t s) =
    let t' = map-Var-Fiber Δp Γp V t
        s' = map-Var-Fiber Δp Γp V s
    in app t' s'
  map-Var-Fiber Δp Γp V tt = tt
  map-Var-Fiber Δp Γp V (left t) =
    let t' = map-Var-Fiber Δp Γp V t
    in left t'
  map-Var-Fiber Δp Γp V (right t) =
    let t' = map-Var-Fiber Δp Γp V t
    in right t'
  map-Var-Fiber Δp Γp V (either t s u) =
    let t' = map-Var-Fiber Δp Γp V t
        s' = map-Var-Fiber (Δp , _) (Γp , _) (λ {(suc v) -> suc (V v)
                              ; none -> none
                              ; (zero v w) -> (zero v w)}) s
        u' = map-Var-Fiber (Δp , _) (Γp , _) (λ {(suc v) -> suc (V v)
                              ; none -> none
                              ; (zero v w) -> (zero v w)}) u
    in either t' s' u'
  map-Var-Fiber Δp Γp V [] = []
  map-Var-Fiber Δp Γp V (t ∷ s) =
    let t' = map-Var-Fiber Δp Γp V t
        s' = map-Var-Fiber Δp Γp V s
    in t' ∷ s'
  map-Var-Fiber Δp Γp V (rec-Lst t s u) =
    let t' = map-Var-Fiber Δp Γp V t
        s' = map-Var-Fiber Δp Γp V s
        u' = map-Var-Fiber ((Δp , _) , _) ((Γp , _) , _) (λ {(suc (suc v)) -> suc (suc (V v))
                              ; none -> none
                              ; (suc (zero v w)) -> (suc (zero v w))
                              ; (suc none) -> (suc none)
                              ; (zero v w) -> (zero v w)}) u
    in rec-Lst t' s' u'


  ⟨ map-Var {Γ = Γ} V (incl t) ⟩ p x Xp Γp = map-Var-Fiber (local-Proof Γp) (local-Proof (π-Ctx-Proof Γ _)) (λ vₗ -> V x (π-Ctx-Proof Γ (⦗ p ⦘₊ ∷ _)) Γp vₗ ) (t p x Xp ((π-Ctx-Proof Γ (⦗ p ⦘₊ ∷ _))))


  map-Var' : ∀{p} -> isLocal p Γ -> isLocal p Δ -> (∀{A qs} -> Γ ⊢Var A GlobalFiber[ p ∷ qs ] -> Δ ⊢Var A GlobalFiber[ p ∷ qs ])
            -> Γ ⊢ X GlobalFibered[ ps ] -> Δ ⊢ X GlobalFibered[ ps ]
  map-Var' = {!!}

  resVar : ∀{qs rs ps ps'} -> rs ≤ qs -> Γ ⊢Var A GlobalFiber[ ps <> (qs ∷ ps') ] -> Γ ⊢Var A GlobalFiber[ ps <> (rs ∷ ps') ]
  resVar {ps = []} pp (zero x x₁) = {!!}
  resVar {ps = []} pp (suc v) = {!!}
  resVar {ps = []} pp (res v) = {!!}
  resVar {ps = []} pp none = {!!}
  resVar {ps = p ∷ ps} pp (zero x x₁) = {!!}
  resVar {ps = p ∷ ps} pp (suc v) = {!!}
  resVar {ps = p ∷ ps} pp (res v) = {!!}
  resVar {ps = p ∷ ps} pp none = {!!}

  π-subset : ∀{p q} -> ⦗ p ⦘₊ ≤ q -> π X ∣ ⦗ p ⦘₊ , [] ↦ A Type -> π X ∣ q , [] ↦ B Type -> A ≡ B
  π-subset pp (proj-＠ x done) (proj-＠ x₂ done) = {!!}
  π-subset pp (proj-＠ x done) (proj-＠-≠ x₂) = {!!}
  π-subset pp (proj-＠-≠ x) (proj-＠ x₁ x₂) = {!!}
  π-subset pp (proj-＠-≠ x) (proj-＠-≠ x₁) = {!!}
  π-subset pp (P₁ ⇒ P₂) (Q ⇒ Q₁) = {!!}
  π-subset pp (P₁ ×× P₂) (Q ×× Q₁) = {!!}
  π-subset pp (Either P₁ P₂) (Either Q Q₁) = {!!}
  π-subset pp (Tr P₁) (Tr Q) = {!!}
  π-subset pp (Lst P₁) (Lst Q) = {!!}
  π-subset pp Unit Unit = {!!}


  resVar'' : ∀{Γ Δ Δ₀ Δ₁ qs p ps ps' ps''} -> Γ ∣ ⦗ p ⦘₊ ∷ [] ↦ Δ Ctx
          -> Γ ∣ ps <> (qs ∷ ps'') ↦ Δ₀ Ctx
          -> Δ ∣ ps <> (⦗ p ⦘₊ ∷ ps'') ↦ Δ₁ Ctx
          -> ⦗ p ⦘₊ ≤ qs
          -> Δ₀ ⊢Var A GlobalFiber[ ps <> (qs ∷ ps') ]
          -> Δ₁ ⊢Var A GlobalFiber[ ps <> (⦗ p ⦘₊ ∷ ps') ]
  resVar'' {ps = []} (P , p0) (Q , qq) (R , proj-＠ x₁ done) pp (zero {ps = []} x (proj-＠ x₂ done)) = zero x (proj-＠ {!!} {!!})
  resVar'' {ps = []} (P , p0) (Q , qq) (R , proj-＠ x₁ done) pp (zero {ps = []} x (proj-＠-≠ x₂)) = zero x {!!}
  resVar'' {ps = []} (P , p0) (Q , qq) (R , proj-＠ x₁ done) pp (zero {ps = x₂ ∷ ps} x y) = zero x {!!}
  -- resVar'' {ps = []} (P , p0) (Q , qq) (R , proj-＠ x₁ done) pp (zero x y) = zero x {!!}
  resVar'' {ps = []} (P , p0) (Q , qq) (R , proj-＠-≠ x₁) pp (zero x (proj-＠ x₂ x₃)) = zero x {!!}
  resVar'' {ps = []} (P , p0) (Q , qq) (R , proj-＠-≠ x₁) pp (zero x (proj-＠-≠ x₂)) = zero x {!!}
  resVar'' {ps = []} P Q R pp (suc v) = {!!}
  resVar'' {ps = []} P Q R pp (res v) = {!!}
  resVar'' {ps = []} P Q R pp none = {!!}
  resVar'' {ps = p ∷ ps} P Q R pp v = {!!}

{-
  resVar' : ∀{Γ Δ₀ Δ₁ qs rs ps ps' ps''} -> Γ ∣ ps <> (qs ∷ ps'') ↦ Δ₀ Ctx -> Γ ∣ ps <> (rs ∷ ps'') ↦ Δ₁ Ctx  -> rs ≤ qs -> Δ₀ ⊢Var A GlobalFiber[ ps <> (qs ∷ ps') ] -> Δ₁ ⊢Var A GlobalFiber[ ps <> (rs ∷ ps') ]
  resVar' {ps = []} (P0 , x₂) (P1 , x₃) pp (zero {ps = []} x (proj-＠ a done)) = zero x (proj-＠ {!!} {!!})
  resVar' {ps = []} (P0 , x₂) (P1 , x₃) pp (zero {ps = []} x (proj-＠-≠ a)) = zero x {!x₁!}
  resVar' {ps = []} (P0 , x₂) (P1 , x₃) pp (zero {ps = (p ∷ ps)} x x₁) = zero x {!!}
  resVar' {ps = []} P0 P1 pp (suc v) = {!!}
  resVar' {ps = []} P0 P1 pp (res v) = {!!}
  resVar' {ps = []} P0 P1 pp none = {!!}
  resVar' {ps = p ∷ ps} P0 P1 pp v = {!!}
  -}⦗ p ⦘₊


  -- resVar p (zero x p) = zero {!!} ?
  -- resVar p (suc v) = suc (resVar p v)
  -- resVar {ps = ps} rel (res {p = p} v) = res (resVar {ps = p ∷ ps} rel v)

  -- transRes-GlobalFibered : ∀{qs rs} -> rs ≤ qs -> Γ ,[ qs ] ⊢ X GlobalFibered[ ps ] -> Γ ,[ rs ] ⊢ X GlobalFibered[ ps ]
  -- -- transRes-GlobalFibered {qs = qs} {rs = rs} pp t = map-Var (λ {q∈ps (stepRes Γp) (stepRes Δp) (res v) -> res (let v' = resVar {ps = []} pp v in projVar1 {ps = rs ∷ []} (unique-π-Ctx-≤ pp Γp Δp ) v')}) t
  -- transRes-GlobalFibered {qs = qs} {rs = rs} pp t = map-Var (λ {q∈ps (stepRes Γp) (stepRes Δp) (res v) -> res (resVar' {ps = []} Γp Δp pp v)}) t

  transRes'-GlobalFibered : ∀{qs} -> Γ ∣ ⦗ p ⦘₊ ∷ [] ↦ Δ Ctx -> ⦗ p ⦘₊ ≤ qs -> Γ ,[ qs ] ⊢ X GlobalFibered[ ps ] -> Δ ,[ ⦗ p ⦘₊ ] ⊢ X GlobalFibered[ ps ]
  transRes'-GlobalFibered P pp t = map-Var (λ {q∈ps (stepRes Γp) (stepRes Δp) (res v) -> res (let v' = resVar'' {ps = []} P Γp Δp pp v in v')}) t
  -- projVar1 {ps = _ ∷ []} (unique-π-Ctx-≤ pp Γp Δp ) v')}) t


  cong-GlobalFibered : ∀{Γ Δ} -> Γ ≡ Δ -> Γ ⊢ X GlobalFibered[ ps ] -> Δ ⊢ X GlobalFibered[ ps ]
  cong-GlobalFibered {X = X} {ps = ps} p = transp-≡ (cong-≡ (λ ξ -> ξ ⊢ X GlobalFibered[ ps ]) p)

  cong-Type-GlobalFibered : ∀{X Y} -> X ≡ Y -> Γ ⊢ X GlobalFibered[ ps ] -> Γ ⊢ Y GlobalFibered[ ps ]
  cong-Type-GlobalFibered {Γ = Γ} {ps = ps} p = transp-≡ (cong-≡ (λ ξ -> Γ ⊢ ξ GlobalFibered[ ps ]) p)

{-


  --------------------------------------------------------------
  -- Reproducing global term constructors, locally
  --------------------------------------------------------------
  --

  -------------------
  -- tt

  tt-GlobalFibered : Γ ⊢ Unit GlobalFibered[ ps ]
  tt-GlobalFibered = incl λ { p x Unit Γp → tt}

  tt-＠-GlobalFibered : Γ ⊢ Unit ＠ U GlobalFibered[ ps ]
  tt-＠-GlobalFibered = incl λ { p x (proj-＠ x₁ done) Γp → tt
                              ; p x (proj-＠-≠ x₁) Γp → tt}


  -------------------
  -- lambda

  lam-GlobalFibered : Γ , X ⊢ Y GlobalFibered[ ps ] -> Γ ⊢ X ⇒ Y GlobalFibered[ ps ]
  lam-GlobalFibered t = incl λ {p p∈ps (X↦A ⇒ Y↦B) Γ↦Δ -> lam (⟨ t ⟩ p p∈ps Y↦B (Γ↦Δ , X↦A)) }


  -------------------
  -- app

  app-GlobalFibered : Γ ⊢ X ⇒ Y GlobalFibered[ ps ]
                   -> Γ ⊢ X GlobalFibered[ ps ]
                   -> Γ ⊢ Y GlobalFibered[ ps ]
  ⟨ app-GlobalFibered {X = X} t s ⟩ p p∈ps Y↦Y' Γ↦Δ =
    let X' = π-Type X (⦗ p ⦘₊ , [])
        X↦X' = π-Type-Proof X ⦗ p ⦘₊
        t' = (⟨ t ⟩ p p∈ps (X↦X' ⇒ Y↦Y') Γ↦Δ)
        s' = (⟨ s ⟩ p p∈ps X↦X' Γ↦Δ)
    in app t' s'

  -------------------
  -- letin

  letin-GlobalFibered : Γ ⊢ X GlobalFibered[ ps ]
                     -> Γ , X ⊢ Y GlobalFibered[ ps ]
                     -> Γ ⊢ Y GlobalFibered[ ps ]
  letin-GlobalFibered t s = app-GlobalFibered (lam-GlobalFibered s) t

  -------------------
  -- mod-box

  box-GlobalFibered : Γ ,[ qs ] ⊢ X GlobalFibered[ allProcs This ]
                     -> Γ ⊢ ◻ X ＠ qs GlobalFibered[ ps ]
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠ x done) Γ↦Δ =
    let t' = transRes'-GlobalFibered Γ↦Δ x t
    in box' {p = p} t'
    -- in box' {p = p} {!!} --  (map-Var (λ {q∈ps (stepRes Γp) (stepRes Δp) (res v) -> res (transp-Ctx-Var ((idempotent-local' (local-Proof Γ↦Δ) Δp)) (transp-Ctx-Var (unique-π-Ctx Γp Γ↦Δ) v))}) t')
    -- in box' {p = p} (map-Var (λ {q∈ps (stepRes Γp) (stepRes Δp) (res v) -> res (transp-Ctx-Var ((idempotent-local' (local-Proof Γ↦Δ) Δp)) (transp-Ctx-Var (unique-π-Ctx Γp Γ↦Δ) v))}) t')
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠-≠ x) Γ↦Δ = tt

{-
{-

{-

{-
{-

  multibox : ∀{ν : ◯ ⟶ ▲ U} -> ∀{Γ i X ps} -> addRestr ν (Γ , i) ⊢ X GlobalFibered[ allProcs This ]
             -> Γ ⊢ F-Type ν X ＠ i GlobalFibered[ ps ]
  multibox {ν = `[]` ⨾ id'} t = box-GlobalFibered t
  multibox {ν = `[]` ⨾ `＠` U ⨾ ν} t = multibox {ν = ν} (box-GlobalFibered t)

  multibox' : ∀{ν : ◯ ⟶ ◯} -> ∀{Γ X ps} -> addRestr ν Γ ⊢ X GlobalFibered[ allProcs This ]
             -> Γ ⊢ F-Type ν X GlobalFibered[ ps ]
  multibox' {ν = id'} t = incl λ {p p∈ps Xp Γp -> ⟨ t ⟩ p (inAllProcs This) Xp Γp}
  multibox' {ν = `[]` ⨾ `＠` U ⨾ ν} t = multibox' {ν = ν} (box-GlobalFibered t)


  -------------------
  -- pure
  pure-GlobalFibered : Γ ⊢ X GlobalFibered[ ps ]
                     -> Γ ⊢ Tr X GlobalFibered[ ps ]
  pure-GlobalFibered t = incl λ { p x (Tr Xp) Γp → pure (⟨ t ⟩ p x Xp Γp)}

  pure-＠-GlobalFibered : Γ ⊢ A ＠ U GlobalFibered[ ps ]
                     -> Γ ⊢ Tr A ＠ U GlobalFibered[ ps ]
  pure-＠-GlobalFibered t = incl λ { p x (proj-＠ x₁ done) Γp → pure (⟨ t ⟩ p x ((proj-＠ x₁ done)) Γp)
                                   ; p x (proj-＠-≠ x₁) Γp → tt}


  -------------------
  -- seq
  seq-GlobalFibered : Γ ⊢ Tr X GlobalFibered[ ps ]
                      -> Γ , X ⊢ Tr Y GlobalFibered[ ps ]
                      -> Γ ⊢ Tr Y GlobalFibered[ ps ]
  seq-GlobalFibered {X = X} {Y = Y} t s = incl λ
    { p x (Tr Yp) Γp →
      let Xp = π-Type-Proof X (⦗ p ⦘₊)
      in seq (⟨ t ⟩ p x (Tr Xp) Γp) (⟨ s ⟩ p x (Tr Yp) (Γp , Xp))
    }

  seq-＠-GlobalFibered : Γ ⊢ Tr A ＠ U GlobalFibered[ ps ]
                      -> Γ , A ＠ U ⊢ Tr B ＠ U GlobalFibered[ ps ]
                      -> Γ ⊢ Tr B ＠ U GlobalFibered[ ps ]
  seq-＠-GlobalFibered t s = incl λ
    { p x (proj-＠ x₁ done) Γp → seq (⟨ t ⟩ p x (proj-＠ x₁ done) Γp) (⟨ s ⟩ p x (proj-＠ x₁ done) (Γp , (proj-＠ x₁ done)))
    ; p x (proj-＠-≠ x₁) Γp → tt}


  -------------------
  -- left
  left-＠-GlobalFibered : Γ ⊢ A ＠ U GlobalFibered[ ps ]
                       -> Γ ⊢ Either A B ＠ U GlobalFibered[ ps ]
  left-＠-GlobalFibered t = incl λ
    { p x (proj-＠ x₁ done) Γp → left (⟨ t ⟩ p x ((proj-＠ x₁ done)) Γp)
    ; p x (proj-＠-≠ x₁) Γp → tt}

  left-GlobalFibered : Γ ⊢ X GlobalFibered[ ps ]
                      -> Γ ⊢ Either X Y GlobalFibered[ ps ]
  left-GlobalFibered {X = X} {Y = Y} t = incl λ
    { p x (Either Xp Yp) Γp → left (⟨ t ⟩ p x Xp Γp)
    }

  -------------------
  -- right
  right-＠-GlobalFibered : Γ ⊢ B ＠ U GlobalFibered[ ps ]
                       -> Γ ⊢ Either A B ＠ U GlobalFibered[ ps ]
  right-＠-GlobalFibered t = incl λ
    { p x (proj-＠ x₁ done) Γp → right (⟨ t ⟩ p x ((proj-＠ x₁ done)) Γp)
    ; p x (proj-＠-≠ x₁) Γp → tt}

  right-GlobalFibered : Γ ⊢ Y GlobalFibered[ ps ]
                      -> Γ ⊢ Either X Y GlobalFibered[ ps ]
  right-GlobalFibered {Y = Y} {X = X} t = incl λ
    { p x (Either Xp Yp) Γp → right (⟨ t ⟩ p x Yp Γp)
    }

  -------------------
  -- either
  either-＠-GlobalFibered : Γ ⊢ Either A B ＠ U GlobalFibered[ ps ]
                         -> Γ , A ＠ U ⊢ C ＠ U GlobalFibered[ ps ]
                         -> Γ , B ＠ U ⊢ C ＠ U GlobalFibered[ ps ]
                         -> Γ ⊢ C ＠ U GlobalFibered[ ps ]
  either-＠-GlobalFibered t s u = incl λ
    { p x (proj-＠ x₁ done) Γp → either (⟨ t ⟩ p x (proj-＠ x₁ done) Γp) (⟨ s ⟩ p x (proj-＠ x₁ done) (Γp , (proj-＠ x₁ done))) ((⟨ u ⟩ p x (proj-＠ x₁ done) (Γp , (proj-＠ x₁ done))))
    ; p x (proj-＠-≠ x₁) Γp → tt}

  either-GlobalFibered : Γ ⊢ Either X Y GlobalFibered[ ps ]
                      -> Γ , X ⊢ Z GlobalFibered[ ps ]
                      -> Γ , Y ⊢ Z GlobalFibered[ ps ]
                      -> Γ ⊢ Z GlobalFibered[ ps ]
  either-GlobalFibered {X = X} {Y = Y} t s u = incl λ
    { p x Zp Γp →
      let Xp = π-Type-Proof X (⦗ p ⦘₊)
          Yp = π-Type-Proof Y (⦗ p ⦘₊)
      in either (⟨ t ⟩ p x (Either Xp Yp) Γp) (⟨ s ⟩ p x Zp (Γp , Xp)) ((⟨ u ⟩ p x Zp (Γp , Yp)))
    }


  -------------------
  -- []
  []-＠-GlobalFibered : Γ ⊢ Lst A ＠ U GlobalFibered[ ps ]
  []-＠-GlobalFibered = incl λ { p x (proj-＠ x₁ done) Γp → []
                              ; p x (proj-＠-≠ x₁) Γp → tt}

  []-GlobalFibered : Γ ⊢ Lst X GlobalFibered[ ps ]
  []-GlobalFibered {X = X} = incl λ
    { p x (Lst Xp) Γp → []
    }

  -------------------
  -- _∷_
  _∷_-＠-GlobalFibered : Γ ⊢ A ＠ U GlobalFibered[ ps ]
                    -> Γ ⊢ Lst A ＠ U GlobalFibered[ ps ]
                    -> Γ ⊢ Lst A ＠ U GlobalFibered[ ps ]
  _∷_-＠-GlobalFibered t s = incl λ
    { p x (proj-＠ x₁ done) Γp → (⟨ t ⟩ p x ((proj-＠ x₁ done)) Γp) ∷ (⟨ s ⟩ p x ((proj-＠ x₁ done)) Γp)
    ; p x (proj-＠-≠ x₁) Γp → tt}

  _∷_-GlobalFibered : Γ ⊢ X GlobalFibered[ ps ]
                  -> Γ ⊢ Lst X GlobalFibered[ ps ]
                  -> Γ ⊢ Lst X GlobalFibered[ ps ]
  _∷_-GlobalFibered {X = X} t s = incl λ
    { p x (Lst Xp) Γp → _∷_ (⟨ t ⟩ p x Xp Γp) (⟨ s ⟩ p x (Lst Xp) Γp)
    }


  -------------------
  -- rec-Lst
  rec-Lst-＠-GlobalFibered : Γ ⊢ Lst A ＠ U GlobalFibered[ ps ]
                         -> Γ ⊢ C ＠ U GlobalFibered[ ps ]
                         -> (Γ , A ＠ U) , C ＠ U ⊢ C ＠ U GlobalFibered[ ps ]
                         -> Γ ⊢ C ＠ U GlobalFibered[ ps ]
  rec-Lst-＠-GlobalFibered t s u = incl λ
    { p x (proj-＠ x₁ done) Γp → rec-Lst (⟨ t ⟩ p x (proj-＠ x₁ done) Γp) (⟨ s ⟩ p x (proj-＠ x₁ done) Γp) ((⟨ u ⟩ p x (proj-＠ x₁ done) ((Γp , (proj-＠ x₁ done)) , (proj-＠ x₁ done))))
    ; p x (proj-＠-≠ x₁) Γp → tt}


  rec-Lst-GlobalFibered : Γ ⊢ Lst X GlobalFibered[ ps ]
                      -> Γ ⊢ Z GlobalFibered[ ps ]
                      -> (Γ , X) , Z ⊢ Z GlobalFibered[ ps ]
                      -> Γ ⊢ Z GlobalFibered[ ps ]
  rec-Lst-GlobalFibered {X = X} {Z = Z} t s u = incl λ
    { p x Zp Γp →
      let Xp = π-Type-Proof X (⦗ p ⦘₊)
      in rec-Lst (⟨ t ⟩ p x (Lst Xp) Γp) (⟨ s ⟩ p x Zp Γp) ((⟨ u ⟩ p x Zp ((Γp , Xp) , Zp)))
    }


  -------------------
  -- broadcast

  broadcast-GlobalFibered : Γ ⊢ ◻ X ＠ qs GlobalFibered[ ps ]
                            -> Γ ⊢ Tr X GlobalFibered[ ps ]
  ⟨ broadcast-GlobalFibered {X = X} {qs = qs} t ⟩ p x (Tr Xp) Γp with p ∈? ⟨ fst qs ⟩
  ... | no p∉qs = recv Xp
  ... | yes p∈qs = send Xp (⟨ t ⟩ p x (proj-＠ (incl (incl f)) done) Γp)
    where
      f = λ { _ here → p∈qs}

-}
-}
-}
-}
-}
-}
