
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.StdProc.Translation where

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
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Order.StrictOrder.Base

open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties
open import KamiCore.Language.StdProc.Definition



F₄ : Std𝔓roc -> Chor𝔓roc _
F₄ This = Std𝔓roc/Definition.[Std𝔓roc/Definition::Private].Super This

macro 𝔉₄ = #structureOn F₄

module _ (This : Std𝔓roc) where
  open Std𝔓roc/Definition This
  open [Std𝔓roc/Definition::Private] using (Super)
  open [Std𝔓roc/Definition::Type] hiding (A ; B)
  open [Std𝔓roc/Definition::Ctx] hiding (Γ)
  open [Std𝔓roc/Definition::Term]

  open Chor𝔓roc/Definition Super hiding (Super)
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type] renaming (⊢Type to Chor𝔓roc⊢Type)
  open [Chor𝔓roc/Definition::Ctx] renaming (⊢Ctx to Chor𝔓roc⊢Ctx)
  open [Chor𝔓roc/Definition::Term] renaming (_⊢_ to _Chor𝔓roc⊢_)
  open Chor𝔓roc/Properties Super

  par-𝔉₄ : Param Super -> Param This
  par-𝔉₄ x = x

  --------------------------------------------------------------------
  -- Types

  ⟦_⟧-FType : Chor𝔓roc⊢Type ◯ -> ⊢Type

  {-# TERMINATING #-}
  ⟦_⟧-LType : Chor𝔓roc⊢Type ▲ -> LType
  ⟦ ◻ T ⟧-LType = ◻ ⟦ T ⟧-FType
  ⟦ Unit ⟧-LType = Unit
  ⟦ Either T S ⟧-LType = Either ⟦ T ⟧-LType ⟦ S ⟧-LType
  ⟦ T ⇒ S ⟧-LType = ⟦ T ⟧-LType ⇒ ⟦ S ⟧-LType
  ⟦ T ×× S ⟧-LType = ⟦ T ⟧-LType ×× ⟦ S ⟧-LType
  ⟦ Tr T ⟧-LType = Tr ⟦ T ⟧-LType
  ⟦ Lst T ⟧-LType = Lst ⟦ T ⟧-LType

  ⟦_⟧-FType X n = ⟦ π-Type X (⦗ n ⦘₊ , []) ⟧-LType

  ⟪𝔉₄∣_Type⟫ : Chor𝔓roc⊢Type ◯ -> ⊢Type
  ⟪𝔉₄∣_Type⟫ = ⟦_⟧-FType

  -- End Types
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Ctx

  ⟦_⟧-LCtx : ∀ {Δ : Chor𝔓roc⊢Ctx} -> ∀{p} -> isLocal p Δ -> LCtx
  ⟦_⟧-LCtx ε = ε
  ⟦_⟧-LCtx (P , A) = ⟦ P ⟧-LCtx , ⟦ A ⟧-LType
  ⟦_⟧-LCtx (stepRes P) = ⟦ P ⟧-LCtx

  ⟦_⟧-FCtx : ∀ (Γ : Chor𝔓roc⊢Ctx) -> ⊢Ctx
  ⟦_⟧-FCtx Γ n = ⟦ local-Proof (π-Ctx-Proof Γ (⦗ n ⦘₊ ∷ [])) ⟧-LCtx

  ⟪𝔉₄∣_Ctx⟫ : Chor𝔓roc⊢Ctx -> ⊢Ctx
  ⟪𝔉₄∣_Ctx⟫ = ⟦_⟧-FCtx

  cong-LCtx : ∀{Γ Δ} -> {Γp : isLocal ps Γ} {Δp : isLocal ps Δ}
            -> Γp ≡-Local Δp
            -> ⟦ Γp ⟧-LCtx ≡ ⟦ Δp ⟧-LCtx
  cong-LCtx refl-Local = refl-≡



  remap₃-FCtx : ∀{Δ ps p n A} -> ⟦ local-Proof (π-Ctx-Proof Δ ((p ∷ ps) <> (⦗ n ⦘₊ ∷ []))) ⟧-LCtx ⊢Var A Locally
                             -> ⟦ local-Proof (π-Ctx-Proof Δ (p ∷ ps)) ⟧-LCtx ⊢ A Locally
  remap₃-FCtx {Δ = ε} {p} {ns} t = var t
  remap₃-FCtx {Δ = Δ ,[ x ]} {p} {ns} t = remap₃-FCtx {Δ = Δ} {ps = ns ∷ p} t
  remap₃-FCtx {Δ = Δ , X} {ps = ps} {p} {n} zero with γ-Type X (p , ps <> (⦗ n ⦘₊ ∷ [])) | drop-γ {X = X} {p = p} {ps} {⦗ n ⦘₊}
  ... | Y | (no refl-≡) = tt
  ... | Y | (yes refl-≡) = var zero
  remap₃-FCtx {Δ = Δ , x} {p} {ns} (suc v) = wk (remap₃-FCtx {Δ = Δ} v)

  remap-FCtx : ∀{Δ ps p n A} -> ⟦ local-Proof (π-Ctx-Proof Δ ((p ∷ ps) <> (⦗ n ⦘₊ ∷ []))) ⟧-LCtx ⊢ A Locally
                             -> ⟦ local-Proof (π-Ctx-Proof Δ (p ∷ ps)) ⟧-LCtx ⊢ A Locally
  remap-FCtx {Δ = Δ} {ps = ps} {p} {n} t = subst (λ _ -> remap₃-FCtx {Δ = Δ} {ps = ps} {p} {n}) t


  -- NOTE: Not needed anymore since we have the remap-FCtx functions above
{-
  eval₃-FCtx : ∀{Δ ps p n} -> ⟦ local-Proof (π-Ctx-Proof Δ ((p ∷ ps) <> (⦗ n ⦘₊ ∷ []))) ⟧-LCtx ≡ ⟦ local-Proof (π-Ctx-Proof Δ (p ∷ ps)) ⟧-LCtx
  eval₃-FCtx {Δ = ε} {p} {ns} = refl-≡
  eval₃-FCtx {Δ = Δ ,[ x ]} {p} {ns} = eval₃-FCtx {Δ = Δ} {ps = ns ∷ p}
  eval₃-FCtx {Δ = Δ , x} {p} {ns} = cong₂-≡ _,_ (eval₃-FCtx {Δ = Δ} {p} {ns}) {!!} 
  -- {!!} -- cong-≡ (λ ξ -> ξ , _) (eval₃-FCtx {Δ = Δ} {p} {ns})

  eval₂-FCtx : ∀{Δ p n} -> ⟦ local-Proof (π-Ctx-Proof (Δ ,[ ⦗ p ⦘₊ ]) (⦗ n ⦘₊ ∷ [])) ⟧-LCtx ≡ ⟦ local-Proof (π-Ctx-Proof Δ (⦗ p ⦘₊ ∷ [])) ⟧-LCtx
  eval₂-FCtx {Δ = Δ} {p} {n} =
    ⟦ local-Proof (π-Ctx-Proof (Δ ,[ ⦗ p ⦘₊ ]) (⦗ n ⦘₊ ∷ [])) ⟧-LCtx

    ⟨ refl-≡ ⟩-≡

    ⟦ local-Proof (stepRes (π-Ctx-Proof Δ (⦗ p ⦘₊ ∷ ⦗ n ⦘₊ ∷ []))) ⟧-LCtx

    ⟨ refl-≡ ⟩-≡

    ⟦ local-Proof (π-Ctx-Proof Δ (⦗ p ⦘₊ ∷ ⦗ n ⦘₊ ∷ [])) ⟧-LCtx

    ⟨ eval₃-FCtx {Δ = Δ} {ps = []} ⟩-≡

    ⟦ local-Proof (π-Ctx-Proof Δ (⦗ p ⦘₊ ∷ [])) ⟧-LCtx

    ∎-≡

  eval-FCtx : ∀{Δ p n} -> ⟦ Δ ,[ ⦗ p ⦘₊ ] ⟧-FCtx n ≡ ⟦ local-Proof (π-Ctx-Proof Δ (⦗ p ⦘₊ ∷ [])) ⟧-LCtx
  eval-FCtx {Δ = Δ} = eval₂-FCtx {Δ = Δ}
  -}


  -- End Ctx
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Variables

  -- π-empty-or-not : ∀{Γ X B p} -> π X ∣ p , [] ↦ B Type -> (Γ ⊢ ⟦ B ⟧-LType Locally) +-𝒰 (¬(p ∼ ⊥))
  -- π-empty-or-not (proj-＠ x x₁ x₂) = right x
  -- π-empty-or-not (proj-＠-≠ x) = left tt
  -- π-empty-or-not (P₁ ⇒ P₂) with π-empty-or-not P₂
  -- ... | no x = no (lam x)
  -- ... | yes x = yes x
  -- π-empty-or-not (P₁ ×× P₂) with π-empty-or-not P₂
  -- ... | yes x = yes x
  -- ... | no x with π-empty-or-not P₁
  -- ... | yes y = yes y
  -- ... | no y = no (y , x)
  -- π-empty-or-not (Either P₁ P₂) = {!!}
  -- π-empty-or-not (Tr P₁) = {!!}
  -- π-empty-or-not (Lst P₁) = {!!}
  -- π-empty-or-not Unit = {!!}


{-
  π-term-preserve-≤ : ∀{Γ X A B p q} -> p ≤ q
                 -> π X ∣ p , [] ↦ A Type
                 -> π X ∣ q , [] ↦ B Type
                 -> Γ ⊢ ⟦ A ⟧-LType Locally
                 -> Γ ⊢ ⟦ B ⟧-LType Locally
  π-term-preserve-≤ q≤p (proj-＠ x done) (proj-＠ x₂ done) t = t
  π-term-preserve-≤ q≤p (proj-＠ x done) (proj-＠-≠ x₂) t = {!!} -- ⊥-elim (x₂ (q≤p ⟡ x))
  π-term-preserve-≤ q≤p (proj-＠-≠ x) (proj-＠ x₁ done) t = {!!}
  π-term-preserve-≤ q≤p (proj-＠-≠ x) (proj-＠-≠ x₁) t = {!!}
  π-term-preserve-≤ q≤p (p ⇒ p₁) (q ⇒ q₁) t = {!!}
  π-term-preserve-≤ q≤p (p ×× p₁) (q ×× q₁) t = {!!}
  π-term-preserve-≤ q≤p (Either p p₁) (Either q q₁) t = {!!}
  π-term-preserve-≤ q≤p (Tr p) (Tr q) t = {!!}
  π-term-preserve-≤ q≤p (Lst p) (Lst q) t = {!!}
  π-term-preserve-≤ q≤p Unit Unit t = {!!}

-}





  tπ' : ∀{X B Γ p} -> π X ∣ p , [] ↦ B Type -> Γ ⊢ ⟦ ◻ X ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tπ' {p = ([] since []) , ()} P t
  tπ' {X = X} {p = ((x₁ ∷ []) since [-]) , done} P t with unique-π P (π-Type-Proof X (⦗ x₁ ⦘₊))
  ... | refl-≡ = proj t x₁
  tπ' {X = X} {p = ((x₁ ∷ x ∷ p) since uniquep) , p≁⊥} P t = {!!}






  tω : ∀{A B ps Γ} -> ω A ∣ ps ↦ B Type -> Γ ⊢ ⟦ A ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally


  -- tπ {X = X} {p = p} P t = tω (split-π P) (tπ' (π-Type-Proof X p) t)
  tπ : ∀{X B p ps Γ} -> π X ∣ p , ps ↦ B Type -> Γ ⊢ ⟦ ◻ X ⟧-LType Locally -> Γ ⊢ ⟦ B ⟧-LType Locally
  tπ {X = X} {p = p} {[]} P t = tπ' P t
  tπ {X = .(_ ＠ _)} {p = p} {x ∷ ps} (proj-＠ x₁ x₂) t = tω x₂ (tπ (proj-＠ x₁ done) t)
  tπ {X = .(_ ＠ _)} {p = p} {x ∷ ps} (proj-＠-≠ x₁) t = tt
    -- tω (split-π P) (tπ' (π-Type-Proof X p) t)

  tω done t = t
  tω (proj-◻ x) t = tπ x t
  tω Unit t = t

  tv  : ∀{Δ A p ps} -> (Δp : isLocal p Δ) -> Δ ⊢Var A GlobalFiber[ p ∷ ps ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tv (Δp , A) none = tt -- tϕ x₁ (tω x₂ (var zero))
  tv (Δp , A) (zero P X@(proj-＠ b c)) = (tω c (var zero))
  tv (Δp , A) (zero P (proj-＠-≠ x)) = tt -- tϕ x₁ (tω x₂ (var zero))
  tv (Δp , A) (suc v) = let x = tv Δp v in wk x
  tv (stepRes Δp) (res v) = let x = tv Δp v in x

  -- End Variables
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Term

  transp-Ctx-Locally : ∀{Γ Δ X} -> Γ ≡ Δ -> Γ ⊢ X Locally -> Δ ⊢ X Locally
  transp-Ctx-Locally refl-≡ t = t

  ta : ∀ {Γ X} -> Γ ⊢ X GlobalFibered[ allProcs Super ] -> ⟦ Γ ⟧-FCtx ⊢ ⟦ X ⟧-FType


  tr : ∀ {Δ p A} -> (Δp : isLocal ⦗ p ⦘₊ Δ) -> Δ ⊢ A GlobalFiber[ p ] -> ⟦ Δp ⟧-LCtx ⊢ ⟦ A ⟧-LType Locally
  tr Δp (var v) = tv Δp v
  tr Δp (recv {p = p} x) = recv p
  tr Δp (send {X = X} {p = p} v t)
    with unique-π v (π-Type-Proof X (⦗ p ⦘₊))
  ... | refl-≡ =
    let t' = tr Δp t
    in send t'
  tr {Δ} {p} Δp (box' {X = X} x ) =
    let t' : ⟦ Δ ,[ _ ] ⟧-FCtx ⊢ ⟦ X ⟧-FType
        t' = ta {Γ = Δ ,[ _ ]} x

        -- t2' : ⟦ Δ ,[ ⦗ p ⦘₊ ] ⟧-FCtx ⊢ ⟦ X ⟧-FType
        -- t2' = ta {Γ = Δ ,[ ⦗ p ⦘₊ ]} {!!}

    in box λ n ->
      let t'' = t' n

          -- Δ is already projected to p, so Δ ,[ p ] projected should become again Δ
          t''' : ⟦ Δp ⟧-LCtx ⊢ ⟦ X ⟧-FType n Locally
          t''' =
               transp-Ctx-Locally (cong-LCtx (idempotent-local Δp))
                 (remap-FCtx {Δ = Δ} {ps = []} t'')
                 -- (transp-Ctx-Locally (eval-FCtx {Δ = Δ}) t'')

      in t'''
  tr Δp (pure t) = pure (tr Δp t)
  tr Δp (seq t t₁) = seq (tr Δp t) (tr (Δp , _) t₁)
  tr Δp (lam t) =
    let t' = tr (Δp , _) t
    in lam t'
  tr Δp (app t s) = app (tr Δp t) (tr Δp s)
  tr Δp tt = tt
  tr Δp (left t) = left (tr Δp t)
  tr Δp (right t) = right (tr Δp t)
  tr Δp (either t t₁ t₂) = either ((tr Δp t)) ((tr (Δp , _) t₁)) ((tr (Δp , _) t₂))
  tr Δp [] = []
  tr Δp (t ∷ t₁) = (tr Δp t) ∷ (tr Δp t₁) 
  tr Δp (rec-Lst t t₁ t₂) = rec-Lst ((tr Δp t)) ((tr Δp t₁)) ((tr ((Δp , _) , _) t₂))

  ta {Γ = Γ} {X} ts n = tr (local-Proof (π-Ctx-Proof Γ _)) (⟨ ts ⟩ n (inAllProcs Super) (π-Type-Proof X _) (π-Ctx-Proof Γ _))


  ⟪𝔉₄∣_Term⟫ : ∀ {Γ X} -> Γ ⊢ X GlobalFibered[ allProcs Super ] -> ⟦ Γ ⟧-FCtx ⊢ ⟦ X ⟧-FType
  ⟪𝔉₄∣_Term⟫ = ta

  -- End Term
  --------------------------------------------------------------------


  run-𝔉₄ : {a : Param Super} (p : SubParam Super a) -> Hom-STT (Super at a) (This at a)
  run-𝔉₄ p = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₄∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₄∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₄∣_Term⟫
    }


instance
  isReduction:F₄ : isParamSTTHom Std𝔓roc (Chor𝔓roc _) F₄
  isReduction:F₄ = record
    { param = par-𝔉₄
    ; subparam = λ A _ -> tt
    ; runAt = run-𝔉₄
    }



