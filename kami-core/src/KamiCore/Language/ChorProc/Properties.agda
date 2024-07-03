

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
    π-Type (Either X Y) ps = Either (π-Type X ps) (π-Type Y ps)
    π-Type (X ⇒ Y) ps = π-Type X ps ⇒ π-Type Y ps
    π-Type (X ×× Y)  ps = π-Type X ps ×× π-Type Y ps
    π-Type (Tr X)  ps = Tr (π-Type X ps)
    π-Type (Lst X)  ps = Lst (π-Type X ps)
    π-Type (A ＠ l) (p , ps) with decide-≤ p l
    ... | no x = Unit
    ... | yes x with p ≟ ⊥
    ... | yes x = Unit
    ... | no y = ω-Type A ps

    ω-Type : (A : ⊢Type ▲) -> List (𝒫ᶠⁱⁿ (Proc This)) -> ⊢Type ▲
    ω-Type A [] = A
    -- ω-Type (◻ X) (p ∷ ps) = [ X ∣ p , ps ]◅ π-Type X (p , ps)
    ω-Type (◻ X) (p ∷ ps) = π-Type X (p , ps)
    ω-Type Unit (p ∷ ps) = {!!}
    ω-Type (Either T S)  (x₂ ∷ x₃) = {!!}
    ω-Type (T ⇒ S) (x₂ ∷ x₃) = {!!}
    ω-Type (T ×× S) (x₂ ∷ x₃) = {!!}
    ω-Type (Tr T) (x₁ ∷ x₂) = {!!}
    ω-Type (Lst T) (x₁ ∷ x₂) = {!!}

  mutual
    π-Type-Proof : (X : ⊢Type ◯) -> (ps : (𝒫ᶠⁱⁿ (Proc This)) ×-𝒰 List (𝒫ᶠⁱⁿ (Proc This))) -> π X ∣ ps ↦ π-Type X ps Type
    π-Type-Proof Unit ps = Unit
    π-Type-Proof (Either X Y) ps = Either (π-Type-Proof X ps) (π-Type-Proof Y ps)
    π-Type-Proof (X ⇒ Y) ps = π-Type-Proof X ps ⇒ π-Type-Proof Y ps
    π-Type-Proof (Tr X) ps = Tr (π-Type-Proof X ps)
    π-Type-Proof (Lst X) ps = Lst (π-Type-Proof X ps)
    π-Type-Proof (A ＠ l) (p , ps) with decide-≤ p l
    ... | no x = proj-＠-≠ (left x)
    ... | yes x with p ≟ ⊥
    ... | yes x = proj-＠-≠ (right x)
    ... | no y = proj-＠ y x (ω-Type-Proof A ps)
    π-Type-Proof (T ×× S) ps = {!!}

    ω-Type-Proof : (A : ⊢Type ▲) -> (ps : List (𝒫ᶠⁱⁿ (Proc This))) -> ω A ∣ ps ↦ ω-Type A ps Type
    ω-Type-Proof = {!!}



  π-Ctx : ⊢Ctx -> List (𝒫ᶠⁱⁿ (Proc This)) -> ⊢Ctx
  π-Ctx Γ [] = Γ
  π-Ctx ε (i ∷ is) = ε
  π-Ctx (Γ ,[ x ]) (i ∷ is) = π-Ctx Γ (x ∷ i ∷ is) ,[ x ]
  π-Ctx (Γ , x) (i ∷ is) = π-Ctx Γ (i ∷ is) , π-Type x (i , []) ＠ i

  local-Proof : ∀ {Γ Δ p ps} -> Γ ∣ p ∷ ps ↦ Δ Ctx -> isLocal p Δ
  local-Proof ε = ε
  local-Proof (p , x) = (local-Proof p) , _
  local-Proof (stepRes p) = stepRes (local-Proof p)

  π-Ctx-Proof : (Γ : ⊢Ctx) -> (i : List (𝒫ᶠⁱⁿ (Proc This))) -> Γ ∣ i ↦ π-Ctx Γ i Ctx
  π-Ctx-Proof Γ [] = done
  π-Ctx-Proof ε (i ∷ is) = ε
  π-Ctx-Proof (Γ ,[ x ]) (i ∷ is) = stepRes (π-Ctx-Proof Γ (x ∷ i ∷ is)) 
  π-Ctx-Proof (Γ , x) (i ∷ is) = π-Ctx-Proof Γ (i ∷ is) , π-Type-Proof x (i , [])

  data _≡-Local_ {ps} : {Γ Δ : ⊢Ctx} (Γp : isLocal ps Γ) (Δp : isLocal ps Δ) -> 𝒰 𝑗 where
    refl-Local : ∀{Γ} {Γp : isLocal ps Γ} -> Γp ≡-Local Γp

  idempotent-local : ∀{Δ : ⊢Ctx} (Δp : isLocal ps Δ) -> local-Proof (π-Ctx-Proof Δ (ps ∷ [])) ≡-Local Δp
  idempotent-local Δp = {!!}


  unique-π : ∀{X A B ps} -> π X ∣ ps ↦ A Type -> π X ∣ ps ↦ B Type -> A ≡ B
  unique-π p q = {!!}

  split-π : ∀{p ps} -> π X ∣ p , ps ↦ A Type -> ω π-Type X (p , []) ∣ ps ↦ A Type
  split-π {p = p} (proj-＠ {qs = qs} p≁⊥ x x₁) with decide-≤ p qs
  ... | no x₂ = ⊥-elim (x₂ x)
  ... | yes x₂ with p ≟ ⊥
  ... | yes P = {!!}
  ... | no P = x₁
  split-π {p = p} (proj-＠-≠ {qs = qs} x) with decide-≤ p qs
  split-π {p = p} {[]} (proj-＠-≠ {qs = _} x) | no x₂ = done
  split-π {p = p} {x₁ ∷ ps} (proj-＠-≠ {qs = _} x) | no x₂ = Unit
  ... | yes x₂ with p ≟ ⊥
  split-π {p = p} (proj-＠-≠ {qs = _} (no x)) | yes x₂ | no P = ⊥-elim (x x₂)
  split-π {p = p} (proj-＠-≠ {qs = _} (yes x)) | yes x₂ | no P = ⊥-elim (P x)
  -- ⊥-elim (x x₂)
  split-π {p = p} {[]} (proj-＠-≠ {qs = _} (no x)) | yes x₂ | yes P = done
  split-π {p = p} {x₁ ∷ ps} (proj-＠-≠ {qs = _} (no x)) | yes x₂ | yes P = Unit
  split-π {p = p} {[]} (proj-＠-≠ {qs = _} (yes x)) | yes x₂ | yes P = done
  split-π {p = p} {x₁ ∷ ps} (proj-＠-≠ {qs = _} (yes x)) | yes x₂ | yes P = Unit
  split-π (P ⇒ P₁) = {!!}
  split-π (P ×× P₁) = {!!}
  split-π (Either P P₁) = {!!}
  split-π (Tr P) = {!!}
  split-π (Lst P) = {!!}
  split-π Unit = {!!}

  --------------------------------------------------------------
  -- Properties of variables
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
    lem-13 {Lst X} x (Lst x₁) = {!!}
    lem-13 (proj-＠ p≁⊥ x v) (proj-＠ q≁⊥ x₁ w) = lem-13' v w
    lem-13 (proj-＠ p≁⊥ x v) (proj-＠-≠ x₁) = {!!} -- ⊥-elim (x₁ x)
    lem-13 (proj-＠-≠ x) (proj-＠ q≁⊥ x₁ w) = {!!} -- ⊥-elim (x x₁)
    lem-13 (proj-＠-≠ x) (proj-＠-≠ x₁) = {!Unit!}
    lem-13 (v ⇒ v₁) (w ⇒ w₁) = {!!}
    lem-13 Unit Unit = {!!}

  lem-12 : ∀{p ps qs} -> π X ∣ p , ps ↦ A Type -> π X ∣ p , ps <> qs ↦ B Type -> π (A ＠ p) ∣ p , ps <> qs ↦ B Type
  lem-12 v w = proj-＠ {!!} refl-≤ (lem-13 v w)


  projVar1 : ∀{ps qs} -> Γ ∣ ps ↦ Δ Ctx -> Γ ⊢Var A GlobalFiber[ ps <> qs ] -> Δ ⊢Var A GlobalFiber[ ps <> qs ]
  projVar1 done v = v
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
  commute⁻¹-＠-Exp : ∀ ps -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) GlobalFibered[ qs ] -> Γ ⊢ (A ⇒ B) ＠ ps GlobalFibered[ qs ]
  ⟨ commute⁻¹-＠-Exp ps t ⟩ q q∈qs (proj-＠ q≁⊥ q∈ps done) Γp =
    let t' = (⟨ t ⟩ q q∈qs (proj-＠ q≁⊥ q∈ps done ⇒ proj-＠ q≁⊥ q∈ps done) Γp)
    in t'
  ⟨ commute⁻¹-＠-Exp ps t ⟩ q q∈qs (proj-＠-≠ x) Γp = tt


  commute-＠-Exp : ∀ ps -> Γ ⊢ (A ⇒ B) ＠ ps GlobalFibered[ qs ]
                        -> Γ ⊢ ((A ＠ ps) ⇒ (B ＠ ps)) GlobalFibered[ qs ]
  commute-＠-Exp = {!!}

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

  tt-GlobalFibered : Γ ⊢ Unit GlobalFibered[ ps ]
  tt-GlobalFibered = incl λ { p x Unit Γp → tt}

  tt-＠-GlobalFibered : Γ ⊢ Unit ＠ U GlobalFibered[ ps ]
  tt-＠-GlobalFibered = incl λ { p x (proj-＠ _ x₁ done) Γp → tt
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
  ⟨ box-GlobalFibered {X = X} t ⟩ p p∈ps (proj-＠ p≁⊥ x done) Γ↦Δ =
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


  -------------------
  -- pure
  pure-GlobalFibered : Γ ⊢ X GlobalFibered[ ps ]
                     -> Γ ⊢ Tr X GlobalFibered[ ps ]
  pure-GlobalFibered t = incl λ { p x (Tr Xp) Γp → pure (⟨ t ⟩ p x Xp Γp)}

  pure-＠-GlobalFibered : Γ ⊢ A ＠ U GlobalFibered[ ps ]
                     -> Γ ⊢ Tr A ＠ U GlobalFibered[ ps ]
  pure-＠-GlobalFibered t = incl λ { p x (proj-＠ p≁⊥ x₁ done) Γp → pure (⟨ t ⟩ p x ((proj-＠ p≁⊥ x₁ done)) Γp)
                                   ; p x (proj-＠-≠ x₁) Γp → tt}


  -------------------
  -- seq
  seq-GlobalFibered : Γ ⊢ Tr X GlobalFibered[ ps ]
                      -> Γ , X ⊢ Tr Y GlobalFibered[ ps ]
                      -> Γ ⊢ Tr Y GlobalFibered[ ps ]
  seq-GlobalFibered {X = X} {Y = Y} t s = incl λ
    { p x (Tr Yp) Γp →
      let Xp = π-Type-Proof X (⦗ p ⦘ , [])
      in seq (⟨ t ⟩ p x (Tr Xp) Γp) (⟨ s ⟩ p x (Tr Yp) (Γp , Xp))
    }

  seq-＠-GlobalFibered : Γ ⊢ Tr A ＠ U GlobalFibered[ ps ]
                      -> Γ , A ＠ U ⊢ Tr B ＠ U GlobalFibered[ ps ]
                      -> Γ ⊢ Tr B ＠ U GlobalFibered[ ps ]
  seq-＠-GlobalFibered t s = incl λ
    { p x (proj-＠ p≁⊥ x₁ done) Γp → seq (⟨ t ⟩ p x (proj-＠ p≁⊥ x₁ done) Γp) (⟨ s ⟩ p x (proj-＠ p≁⊥ x₁ done) (Γp , (proj-＠ p≁⊥ x₁ done)))
    ; p x (proj-＠-≠ x₁) Γp → tt}


  -------------------
  -- left
  left-＠-GlobalFibered : Γ ⊢ A ＠ U GlobalFibered[ ps ]
                       -> Γ ⊢ Either A B ＠ U GlobalFibered[ ps ]
  left-＠-GlobalFibered t = incl λ
    { p x (proj-＠ p≁⊥ x₁ done) Γp → left (⟨ t ⟩ p x ((proj-＠ p≁⊥ x₁ done)) Γp)
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
    { p x (proj-＠ p≁⊥ x₁ done) Γp → right (⟨ t ⟩ p x ((proj-＠ p≁⊥ x₁ done)) Γp)
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
    { p x (proj-＠ p≁⊥ x₁ done) Γp → either (⟨ t ⟩ p x (proj-＠ p≁⊥ x₁ done) Γp) (⟨ s ⟩ p x (proj-＠ p≁⊥ x₁ done) (Γp , (proj-＠ p≁⊥ x₁ done))) ((⟨ u ⟩ p x (proj-＠ p≁⊥ x₁ done) (Γp , (proj-＠ p≁⊥ x₁ done))))
    ; p x (proj-＠-≠ x₁) Γp → tt}

  either-GlobalFibered : Γ ⊢ Either X Y GlobalFibered[ ps ]
                      -> Γ , X ⊢ Z GlobalFibered[ ps ]
                      -> Γ , Y ⊢ Z GlobalFibered[ ps ]
                      -> Γ ⊢ Z GlobalFibered[ ps ]
  either-GlobalFibered {X = X} {Y = Y} t s u = incl λ
    { p x Zp Γp →
      let Xp = π-Type-Proof X (⦗ p ⦘ , [])
          Yp = π-Type-Proof Y (⦗ p ⦘ , [])
      in either (⟨ t ⟩ p x (Either Xp Yp) Γp) (⟨ s ⟩ p x Zp (Γp , Xp)) ((⟨ u ⟩ p x Zp (Γp , Yp)))
    }


  -------------------
  -- []
  []-＠-GlobalFibered : Γ ⊢ Lst A ＠ U GlobalFibered[ ps ]
  []-＠-GlobalFibered = incl λ { p x (proj-＠ p≁⊥ x₁ done) Γp → []
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
    { p x (proj-＠ p≁⊥ x₁ done) Γp → (⟨ t ⟩ p x ((proj-＠ p≁⊥ x₁ done)) Γp) ∷ (⟨ s ⟩ p x ((proj-＠ p≁⊥ x₁ done)) Γp)
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
    { p x (proj-＠ p≁⊥ x₁ done) Γp → rec-Lst (⟨ t ⟩ p x (proj-＠ p≁⊥ x₁ done) Γp) (⟨ s ⟩ p x (proj-＠ p≁⊥ x₁ done) Γp) ((⟨ u ⟩ p x (proj-＠ p≁⊥ x₁ done) ((Γp , (proj-＠ p≁⊥ x₁ done)) , (proj-＠ p≁⊥ x₁ done))))
    ; p x (proj-＠-≠ x₁) Γp → tt}


  rec-Lst-GlobalFibered : Γ ⊢ Lst X GlobalFibered[ ps ]
                      -> Γ ⊢ Z GlobalFibered[ ps ]
                      -> (Γ , X) , Z ⊢ Z GlobalFibered[ ps ]
                      -> Γ ⊢ Z GlobalFibered[ ps ]
  rec-Lst-GlobalFibered {X = X} {Z = Z} t s u = incl λ
    { p x Zp Γp →
      let Xp = π-Type-Proof X (⦗ p ⦘ , [])
      in rec-Lst (⟨ t ⟩ p x (Lst Xp) Γp) (⟨ s ⟩ p x Zp Γp) ((⟨ u ⟩ p x Zp ((Γp , Xp) , Zp)))
    }


