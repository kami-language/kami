

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
  cong-Ctx,Var = {!!}

  --------------------------------------------------------------
  -- Proofs on Operations on Types and contexts
  --------------------------------------------------------------

  eval-F-type-right : F-Type (ν ◆' `＠` V ⨾ id') X ≡ (F-Type ν X) ＠ V
  eval-F-type-right = {!!}



  --------------------------------------------------------------
  -- Types and context projections
  --------------------------------------------------------------

  mutual
    π-Type : (X : ⊢Type ◯) -> ((𝒫ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc This))) -> ⊢Type ▲
    π-Type Unit ps = Unit
    π-Type NN ps = NN
    π-Type (Either X Y) ps = Either (π-Type X ps) (π-Type Y ps)
    π-Type (X ⇒ Y) ps = π-Type X ps ⇒ π-Type Y ps
    π-Type (X ×× Y)  ps = π-Type X ps ×× π-Type Y ps
    π-Type (Tr X)  ps = Tr (π-Type X ps)
    π-Type (A ＠ l) (p , ps) with decide-≤ p l
    ... | no x = Unit
    ... | yes x = ω-Type A ps

    ω-Type : (A : ⊢Type ▲) -> List (𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ▲
    ω-Type A [] = A
    -- ω-Type (◻ X) (p ∷ ps) = [ X ∣ p , ps ]◅ π-Type X (p , ps)
    ω-Type (◻ X) (p ∷ ps) = π-Type X (p , ps)
    ω-Type NN (p ∷ ps) = {!!}
    ω-Type Unit (p ∷ ps) = {!!}
    ω-Type (Either T S)  (x₂ ∷ x₃) = {!!}
    ω-Type (T ⇒ S) (x₂ ∷ x₃) = {!!}
    ω-Type (T ×× S) (x₂ ∷ x₃) = {!!}
    ω-Type (Tr T) (x₁ ∷ x₂) = {!!}

  mutual
    π-Type-Proof : (X : ⊢Type ◯) -> (ps : (𝒫ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc This))) -> π X ∣ ps ↦ π-Type X ps Type
    π-Type-Proof Unit ps = Unit
    π-Type-Proof (Either X Y) ps = Either (π-Type-Proof X ps) (π-Type-Proof Y ps)
    π-Type-Proof (X ⇒ Y) ps = π-Type-Proof X ps ⇒ π-Type-Proof Y ps
    π-Type-Proof (Tr X) ps = Tr (π-Type-Proof X ps)
    π-Type-Proof (A ＠ l) (p , ps) with decide-≤ p l
    ... | no x = proj-＠-≠ x
    ... | yes x = proj-＠ x (ω-Type-Proof A ps)
    π-Type-Proof NN ps = {!!}
    π-Type-Proof (T ×× S) ps = {!!}

    ω-Type-Proof : (A : ⊢Type ▲) -> (ps : List (𝒫ᶠⁱⁿ (Proc This))) -> ω A ∣ ps ↦ ω-Type A ps Type
    ω-Type-Proof = {!!}


  --------------------------------------------------------------
  -- Properties of variables and projections
  --------------------------------------------------------------

  mutual
    lem-13' : ∀{ps qs} -> ω C ∣ ps ↦ A Type -> ω C ∣ ps <> qs ↦ B Type -> ω A ∣ ps <> qs ↦ B Type
    lem-13' = {!!}
    -- lem-13' {ps = x ∷ ps} (proj-◻ v) (proj-◻ w) =  ? -- let z = lem-13 v w in proj-[] {!!} z
    -- lem-13' {ps = x ∷ ps} (proj-[] x₁ x₂) (proj-[] x₃ x₄) = proj-[] {!!} (lem-13' x₂ x₄)
    -- lem-13' {ps = []} Unit-▲ x = x
    -- lem-13' {ps = x ∷ ps} Unit-▲ Unit-▲ = Unit-▲
    -- lem-13' done w = w

    lem-13 : ∀{p ps qs} -> π X ∣ p , ps ↦ A Type -> π X ∣ p , ps <> qs ↦ B Type -> ω A ∣ ps <> qs ↦ B Type
    lem-13 {Either X X₁} x (Either x₁ x₂) = {!!}
    lem-13 {X ×× X₁} x (x₁ ×× x₂) = {!!}
    lem-13 {Tr X} x (Tr x₁) = {!!}
    lem-13 (proj-＠ x v) (proj-＠ x₁ w) = lem-13' v w
    lem-13 (proj-＠ x v) (proj-＠-≠ x₁) = ⊥-elim (x₁ x)
    lem-13 (proj-＠-≠ x) (proj-＠ x₁ w) = ⊥-elim (x x₁)
    lem-13 (proj-＠-≠ x) (proj-＠-≠ x₁) = {!Unit!}
    lem-13 (v ⇒ v₁) (w ⇒ w₁) = {!!}
    lem-13 Unit Unit = {!!}

  lem-12 : ∀{p ps qs} -> π X ∣ p , ps ↦ A Type -> π X ∣ p , ps <> qs ↦ B Type -> π (A ＠ p) ∣ p , ps <> qs ↦ B Type
  lem-12 v w = proj-＠ refl-≤ (lem-13 v w)


  projVar1 : ∀{ps qs} -> Γ ∣ ps ↦ Δ Ctx -> Γ ⊢Var A GlobalFiber[ ps <> qs ] -> Δ ⊢Var A GlobalFiber[ ps <> qs ]
  projVar1 (p , v) (none) = none
  projVar1 (p , v) (zero x w) = zero x (lem-12 v w )
  projVar1 (p , x) (suc v) = suc (projVar1 p v)
  projVar1 (stepRes p) (res v) = res (projVar1 p v)

  projVar3 : ∀{p qs} -> Γ ∣ p ∷ [] ↦ Δ Ctx -> Γ ,[ p ] ⊢Var A GlobalFiber[ qs ] -> Δ ,[ p ] ⊢Var A GlobalFiber[ qs ]
  projVar3 p (res v) with projVar1 p (v)
  ... | (w) = res w



  --------------------------------------------------------------
  -- Generic term constructions of the ChorProc calculus
  --------------------------------------------------------------
  --
  commute-＠-Exp : ∀ ps -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) GlobalFibered[ qs ] -> Γ ⊢ (A ⇒ B) ＠ ps GlobalFibered[ qs ]
  ⟨ commute-＠-Exp ps t ⟩ q q∈qs (proj-＠ q∈ps done) Γp =
    let t' = (⟨ t ⟩ q q∈qs (proj-＠ q∈ps done ⇒ proj-＠ q∈ps done) Γp)
    in t'
  ⟨ commute-＠-Exp ps t ⟩ q q∈qs (proj-＠-≠ x) Γp = tt


  map-Var : (∀{qs A} -> Γ ⊢Var A GlobalFiber[ qs ] -> Δ ⊢Var A GlobalFiber[ qs ]) -> Γ ⊢ X GlobalFibered[ ps ] -> Δ ⊢ X GlobalFibered[ ps ]
  map-Var = {!!}


  transRes-GlobalFibered : ∀{qs rs} -> rs ≤ qs -> Γ ,[ qs ] ⊢ X GlobalFibered[ ps ] -> Γ ,[ rs ] ⊢ X GlobalFibered[ ps ]
  transRes-GlobalFibered = {!!}

  cong-GlobalFibered : ∀{Γ Δ} -> Γ ≡ Δ -> Γ ⊢ X GlobalFibered[ ps ] -> Δ ⊢ X GlobalFibered[ ps ]
  cong-GlobalFibered {X = X} {ps = ps} p = transp-≡ (cong-≡ (λ ξ -> ξ ⊢ X GlobalFibered[ ps ]) p)

  cong-Type-GlobalFibered : ∀{X Y} -> X ≡ Y -> Γ ⊢ X GlobalFibered[ ps ] -> Γ ⊢ Y GlobalFibered[ ps ]
  cong-Type-GlobalFibered {Γ = Γ} {ps = ps} p = transp-≡ (cong-≡ (λ ξ -> Γ ⊢ ξ GlobalFibered[ ps ]) p)



  --------------------------------------------------------------
  -- Reproducing global term constructors, locally
  --------------------------------------------------------------
  --

  -------------------
  -- tt

  tt-◯-GlobalFibered : Γ ⊢ Unit GlobalFibered[ ps ]
  tt-◯-GlobalFibered = incl λ { p x Unit Γp → tt}

  tt-▲-GlobalFibered : Γ ⊢ Unit ＠ U GlobalFibered[ ps ]
  tt-▲-GlobalFibered = incl λ { p x (proj-＠ x₁ done) Γp → tt
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
    let X' = π-Type X (⦗ p ⦘ , [])
        X↦X' = π-Type-Proof X (⦗ p ⦘ , [])
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

  box-GlobalFibered : Γ ,[ qs ] ⊢ X GlobalFibered[ ps ]
                     -> Γ ⊢ ◻ X ＠ qs GlobalFibered[ ps ]
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠ x done) Γ↦Δ =
    let t' = transRes-GlobalFibered x t
    in box' {p = p} (map-Var (projVar3 (Γ↦Δ)) t')
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠-≠ x) Γ↦Δ = tt


  multibox : ∀{ν : ◯ ⟶ ▲ U} -> ∀{Γ i X ps} -> addRestr ν (Γ , i) ⊢ X GlobalFibered[ ps ]
             -> Γ ⊢ F-Type ν X ＠ i GlobalFibered[ ps ]
  multibox {ν = `[]` ⨾ id'} t = box-GlobalFibered t
  multibox {ν = `[]` ⨾ `＠` U ⨾ ν} t = multibox {ν = ν} (box-GlobalFibered t)

  multibox' : ∀{ν : ◯ ⟶ ◯} -> ∀{Γ X ps} -> addRestr ν Γ ⊢ X GlobalFibered[ ps ]
             -> Γ ⊢ F-Type ν X GlobalFibered[ ps ]
  multibox' {ν = id'} t = t
  multibox' {ν = `[]` ⨾ `＠` U ⨾ ν} t = multibox' {ν = ν} (box-GlobalFibered t)




