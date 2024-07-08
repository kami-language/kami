
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.TranslationVar where

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
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Properties
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties
open import KamiCore.Language.ChorProc.Properties2
open import KamiCore.Language.ChorProc.Properties3
open import KamiCore.Language.ChorProc.TranslationCtx




module Chor𝔓roc/TranslationVar (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This
  open Chor𝔓roc/Properties2 This
  open Chor𝔓roc/Properties3 This
  open Chor𝔓roc/TranslationCtx This

  open Chor𝔐TT/Definition Super
  open [Chor𝔐TT/Definition::Type] renaming (⊢Type to Chor𝔐TT⊢Type)
  open [Chor𝔐TT/Definition::Ctx] renaming (⊢Ctx to Chor𝔐TT⊢Ctx)
  open [Chor𝔐TT/Definition::Term] renaming (_⊢_ to _Chor𝔐TT⊢_)
  open Chor𝔐TT/Properties Super


  -- TODO: currently these definitions
  -- have to be stated in multiple places,
  -- because otherwise the inference doesn't work.
  -- Merge in a single place.
  private
    pattern []ₛ = (`[]` ⨾ id' , incl `[]`)
    pattern ＠ₛ U  = (`＠` U ⨾ id' , incl (`＠` _))

  --------------------------------------------------------------------
  -- Variables


  local-var-impossible : ∀{b c A} {Γ : Chor𝔐TT⊢Ctx c} -> (Γp : isCtx₂ Γ) -> {μ : b ⟶ ▲ U} {η : c ⟶ ▲ U} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> 𝟘-𝒰
  local-var-impossible (stepRes _ Γp) (suc! v) = local-var-impossible Γp v
  local-var-impossible (stepVar Γp) (suc v) = local-var-impossible Γp v



  transl-Var-▲ : (Γ : Chor𝔐TT⊢Ctx ◯) -> ∀ Γp ->  ∀{U V} -> {A : Chor𝔐TT⊢Type (▲ U)}
              -> Γ ⊢Var⟮ A ∣ (`＠` U ⨾ μ) ⇒ (η) ⟯
              -> rev (transl-Mod3 (`[]` ⨾ `＠` U ⨾ μ)) ≼' rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ (ν ◆' η)))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν))) p) ↦ Δ Ctx
              -> π ⦋ A ⦌-Type ＠ V ∣ p , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) (suc v) PP (Γpp , x₁) Xp =
    let res = transl-Var-▲ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ (`＠` U ⨾ μ) ⟯) (stepVar Γp) {U = U} {V} {A = A} zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp , x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 (μ))) (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
        YY = mkVar-▲ {U = U} {V = V} {ps = (rev (transl-Mod3 (μ)))} {qs = (rev' (transl-Mod3 (ν)))} (μ≼ν ◆-≼'≡ (sym-≡ (rev≡rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ ν))) ∙-≡ cong-≡ (_++-List V ∷ []) (rev≡rev' (transl-Mod3 ν)) )) Xp
-- (transl-Mod3 (`[]` ⨾ `＠` V ⨾ ν))

        -- mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 (`[]` ⨾ ν)))} μ≼ν Xp

        ZZ : (Δ , F-Type μ (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
        ZZ = transp-Ctx-Var (cong-Ctx,Var (sym-≡ (F-prop {μ = μ} {X = (⦋ x ⦌-Type ＠ U)}))) YY

    in updateVar-γ (MakeNot＠ {A = ⦋ x ⦌-Type} {μs = μ} {W =  U}) x₁ ZZ
  transl-Var-▲ {ν = ν} (Γ ∙! ＠ₛ U ∙! []ₛ) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp =
    let
        P1 : cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p) ≡ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p)
        P1 = cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p)
                  ⟨ cons-post (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p ⟩-≡
             (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) <> (p ∷ [])
                  ⟨ cong-≡ (_++-List (p ∷ [])) (eval-r-transl-Mod'' {ϕ₀ = ν ◆' (`[]` ⨾ id')}) ⟩-≡
             (U ∷ rev' (transl-Mod3 (ν ◆ (`[]` ⨾ id')))) <> (p ∷ [])
                  ⟨ cong-≡ (λ ξ -> U ∷ rev' ξ <> (p ∷ [])) (transl-Mod3-drop-[] ν) ⟩-≡
             U ∷ ((rev' (transl-Mod3 ν)) <> (p ∷ []))
                  ⟨ cong-≡ (U ∷_) (sym-≡ (cons-post (rev' (transl-Mod3 ν)) p)) ⟩-≡
             U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ∎-≡

        Γpp' : transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p) ↦ Δ Ctx
        Γpp' = transp-≡ (cong-≡ (λ ξ -> transl-Ctx' Γ Γp ∣ ξ ↦ Δ Ctx) (sym-≡ P1)) Γpp

        result = transl-Var-▲ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp


        result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) P1) result

    in res result'




  transl-Var-◯ : (Γ : Chor𝔐TT⊢Ctx ◯) -> ∀ Γp -> {X : Chor𝔐TT⊢Type ◯}
              -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
              -> rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 (ν ◆' η))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 ν)) p) ↦ Δ Ctx
              -> π ⦋ X ⦌-Type ∣ p , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]

  transl-Var-◯ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) (suc v) PP (Γpp , x₁) Xp =
    let res = transl-Var-◯ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res
  transl-Var-◯ {ν = ν} (Γ ∙! ＠ₛ U ∙! []ₛ) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp =
    let
        P1 : cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p) ≡ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p)
        P1 = cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p)
                  ⟨ cons-post (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p ⟩-≡
             (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) <> (p ∷ [])
                  ⟨ cong-≡ (_++-List (p ∷ [])) (eval-r-transl-Mod'' {ϕ₀ = ν ◆' (`[]` ⨾ id')}) ⟩-≡
             (U ∷ rev' (transl-Mod3 (ν ◆ (`[]` ⨾ id')))) <> (p ∷ [])
                  ⟨ cong-≡ (λ ξ -> U ∷ rev' ξ <> (p ∷ [])) (transl-Mod3-drop-[] ν) ⟩-≡
             U ∷ ((rev' (transl-Mod3 ν)) <> (p ∷ []))
                  ⟨ cong-≡ (U ∷_) (sym-≡ (cons-post (rev' (transl-Mod3 ν)) p)) ⟩-≡
             U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ∎-≡

        Γpp' : transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p) ↦ Δ Ctx
        Γpp' = transp-≡ (cong-≡ (λ ξ -> transl-Ctx' Γ Γp ∣ ξ ↦ Δ Ctx) (sym-≡ P1)) Γpp

        result = transl-Var-◯ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp


        result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) P1) result

    in res result'

  transl-Var-◯ {ν = ν} (Γ ∙⟮ x ∣ μ@(`[]` ⨾ `＠` W ⨾ μs) ⟯) (stepVar Γp) zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp , x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 μ)) ⦋ x ⦌-Type) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        YY = mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 ν))} {!!} μ≼ν Xp

        ZZ : (Δ , F-Type μ ⦋ x ⦌-Type) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        ZZ = transp-Ctx-Var (cong-Ctx,Var (sym-≡ (F-prop {μ = μ} {X = (⦋ x ⦌-Type)}))) YY

    in updateVar-γ (MakeNot＠ {A = ◻ ⦋ x ⦌-Type} {μs = μs} {W = W}) x₁ ZZ
  transl-Var-◯ {ν = `[]` ⨾ `＠` V ⨾ νs} (Γ ∙⟮ x ∣ id' ⟯) (stepVar Γp) zero () {p = p} {Δ = Δ , _} {B = B} (Γpp , x₁) Xp -- = {!!}
  transl-Var-◯ {ν = id'} (Γ ∙⟮ x ∣ id' ⟯) (stepVar Γp) zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp , toplevel x₁) Xp =  (zero id-≼ (proj-＠ refl-≤ (lem-14 x₁ Xp)))




--------------------------------------------------------------------

{-

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.TranslationVar where

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
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Properties
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties
open import KamiCore.Language.ChorProc.Properties2
open import KamiCore.Language.ChorProc.Properties3
open import KamiCore.Language.ChorProc.TranslationCtx




module Chor𝔓roc/TranslationVar (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This
  open Chor𝔓roc/Properties2 This
  open Chor𝔓roc/Properties3 This
  open Chor𝔓roc/TranslationCtx This

  open Chor𝔐TT/Definition Super
  open [Chor𝔐TT/Definition::Type] renaming (⊢Type to Chor𝔐TT⊢Type)
  open [Chor𝔐TT/Definition::Ctx] renaming (⊢Ctx to Chor𝔐TT⊢Ctx)
  open [Chor𝔐TT/Definition::Term] renaming (_⊢_ to _Chor𝔐TT⊢_)
  open Chor𝔐TT/Properties Super


  -- TODO: currently these definitions
  -- have to be stated in multiple places,
  -- because otherwise the inference doesn't work.
  -- Merge in a single place.
  private
    pattern []ₛ = (`[]` ⨾ id' , incl `[]`)
    pattern ＠ₛ U  = (`＠` U ⨾ id' , incl (`＠` _))

  --------------------------------------------------------------------
  -- Variables


  local-var-impossible : ∀{b c A} {Γ : Chor𝔐TT⊢Ctx c} -> (Γp : isCtx₂ Γ) -> {μ : b ⟶ ▲ U} {η : c ⟶ ▲ U} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> 𝟘-𝒰
  local-var-impossible (stepRes _ Γp) (suc! v) = local-var-impossible Γp v
  local-var-impossible (stepVar Γp) (suc v) = local-var-impossible Γp v



  transl-Var-▲ : (Γ : Chor𝔐TT⊢Ctx ◯) -> ∀ Γp ->  ∀{U V} -> {A : Chor𝔐TT⊢Type (▲ U)}
              -> Γ ⊢Var⟮ A ∣ (`＠` U ⨾ μ) ⇒ (η) ⟯
              -> rev (transl-Mod3 (`[]` ⨾ `＠` U ⨾ μ)) ≼' rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ (ν ◆' η)))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν))) ⦗ p ⦘₊) ↦ Δ Ctx
              -> π ⦋ A ⦌-Type ＠ V ∣ ⦗ p ⦘₊ , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) ⦗ p ⦘₊) ]
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) (suc v) PP (Γpp , x₁) Xp =
    let res = transl-Var-▲ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ (`＠` U ⨾ μ) ⟯) (stepVar Γp) {U = U} {V} {A = A} zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp , x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 (μ))) (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) ⦗ p ⦘₊) ]
        YY = mkVar-▲ {U = U} {V = V} {ps = (rev (transl-Mod3 (μ)))} {qs = (rev' (transl-Mod3 (ν)))} (μ≼ν ◆-≼'≡ (sym-≡ (rev≡rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ ν))) ∙-≡ cong-≡ (_++-List V ∷ []) (rev≡rev' (transl-Mod3 ν)) )) Xp
-- (transl-Mod3 (`[]` ⨾ `＠` V ⨾ ν))

        -- mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 (`[]` ⨾ ν)))} μ≼ν Xp

        ZZ : (Δ , F-Type μ (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) ⦗ p ⦘₊) ]
        ZZ = transp-Ctx-Var (cong-Ctx,Var (sym-≡ (F-prop {μ = μ} {X = (⦋ x ⦌-Type ＠ U)}))) YY

    in updateVar-γ x₁ ZZ
  transl-Var-▲ {ν = ν} (Γ ∙! ＠ₛ U ∙! []ₛ) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp =
    let p = ⦗ p ⦘₊
        P1 : cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p) ≡ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p)
        P1 = cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p)
                  ⟨ cons-post (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p ⟩-≡
             (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) <> (p ∷ [])
                  ⟨ cong-≡ (_++-List (p ∷ [])) (eval-r-transl-Mod'' {ϕ₀ = ν ◆' (`[]` ⨾ id')}) ⟩-≡
             (U ∷ rev' (transl-Mod3 (ν ◆ (`[]` ⨾ id')))) <> (p ∷ [])
                  ⟨ cong-≡ (λ ξ -> U ∷ rev' ξ <> (p ∷ [])) (transl-Mod3-drop-[] ν) ⟩-≡
             U ∷ ((rev' (transl-Mod3 ν)) <> (p ∷ []))
                  ⟨ cong-≡ (U ∷_) (sym-≡ (cons-post (rev' (transl-Mod3 ν)) p)) ⟩-≡
             U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ∎-≡

        Γpp' : transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p) ↦ Δ Ctx
        Γpp' = transp-≡ (cong-≡ (λ ξ -> transl-Ctx' Γ Γp ∣ ξ ↦ Δ Ctx) (sym-≡ P1)) Γpp

        result = transl-Var-▲ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp


        result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) P1) result

    in res result'




  transl-Var-◯ : (Γ : Chor𝔐TT⊢Ctx ◯) -> ∀ Γp -> {X : Chor𝔐TT⊢Type ◯}
              -> Γ ⊢Var⟮ X ∣ μ ⇒ η ⟯
              -> rev (transl-Mod3 μ) ≼' rev' (transl-Mod3 (ν ◆' η))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 ν)) p) ↦ Δ Ctx
              -> π ⦋ X ⦌-Type ∣ p , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]

  transl-Var-◯ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp , x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 μ)) ⦋ x ⦌-Type) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        YY = mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 ν))} μ≼ν Xp

        ZZ : (Δ , F-Type μ ⦋ x ⦌-Type) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        ZZ = transp-Ctx-Var (cong-Ctx,Var (sym-≡ (F-prop {μ = μ} {X = (⦋ x ⦌-Type)}))) YY

    in updateVar-γ x₁ ZZ
  transl-Var-◯ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) (suc v) PP (Γpp , x₁) Xp =
    let res = transl-Var-◯ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res
  transl-Var-◯ {ν = ν} (Γ ∙! ＠ₛ U ∙! []ₛ) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp =
    let
        P1 : cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p) ≡ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p)
        P1 = cons (postpend (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p)
 
                 ⟨ cons-post (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) p ⟩-≡
             (rev' (transl-Mod3 (ν ◆' `[]` ⨾ `＠` U ⨾ id'))) <> (p ∷ [])
                  ⟨ cong-≡ (_++-List (p ∷ [])) (eval-r-transl-Mod'' {ϕ₀ = ν ◆' (`[]` ⨾ id')}) ⟩-≡
             (U ∷ rev' (transl-Mod3 (ν ◆ (`[]` ⨾ id')))) <> (p ∷ [])
                  ⟨ cong-≡ (λ ξ -> U ∷ rev' ξ <> (p ∷ [])) (transl-Mod3-drop-[] ν) ⟩-≡
             U ∷ ((rev' (transl-Mod3 ν)) <> (p ∷ []))
                  ⟨ cong-≡ (U ∷_) (sym-≡ (cons-post (rev' (transl-Mod3 ν)) p)) ⟩-≡
             U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ∎-≡

        Γpp' : transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν ◆ (`[]` ⨾ `＠` U ⨾ id')))) p) ↦ Δ Ctx
        Γpp' = transp-≡ (cong-≡ (λ ξ -> transl-Ctx' Γ Γp ∣ ξ ↦ Δ Ctx) (sym-≡ P1)) Γpp

        result = transl-Var-◯ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp


        result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) P1) result

    in res result'



-}
