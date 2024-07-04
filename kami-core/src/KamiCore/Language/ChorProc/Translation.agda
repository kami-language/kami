

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorProc.Translation where

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
open import KamiCore.Language.ChorProc.TranslationVar




F₃ : Chor𝔓roc 𝑗 -> Chor𝔐TT _
F₃ This = Chor𝔓roc/Definition.Super This


module _ (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This
  open Chor𝔓roc/Properties2 This
  open Chor𝔓roc/Properties3 This
  open Chor𝔓roc/TranslationCtx This
  open Chor𝔓roc/TranslationVar This

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

  par-𝔉₃ : Param Super -> Param This
  par-𝔉₃ _ = tt



  -- End Variables
  --------------------------------------------------------------------



  --------------------------------------------------------------------
  -- Terms
  transl-Term-▲ : ∀{ps} {i : ⟨ P ⟩} -> (Γ : Chor𝔐TT⊢Ctx {◯} ◯) -> (Γp : isCtx₂ Γ)
            -> ∀{A} -> Γ ∙! (＠ₛ i) Chor𝔐TT⊢ A
            -> transl-Ctx Γ Γp  ⊢ (⦋ A ⦌-Type ＠ i) GlobalFibered[ ps ]

  transl-Term-◯ : ∀{ps} -> (Γ : Chor𝔐TT⊢Ctx {◯} ◯) -> (Γp : isCtx₂ Γ)
            -> ∀{A} -> Γ Chor𝔐TT⊢ A
            -> transl-Ctx Γ Γp  ⊢ ⦋ A ⦌-Type GlobalFibered[ ps ]

  transl-Term-▲ Γ Γp (var {b = ▲ _} (suc! x) [ incl α₀ ∣ incl α₁ ] αp) = ⊥-elim (local-var-impossible Γp x)
  transl-Term-▲ {i = i} Γ Γp (var {b = ◯} {μ = `＠` j ⨾ μ} (suc! x) α αp) =
    incl (λ p x₁ Xp Γp₁ → (let XX = (transl-Var-▲ {ν = id'} Γ Γp x (transToSublist'₁ α αp) Γp₁ Xp) in var XX))

  transl-Term-▲ Γ Γp tt = tt-＠-GlobalFibered
  transl-Term-▲ Γ Γp (mod []ₛ t) =
    let ts' = transl-Term-◯ _ (stepRes _ (stepRes _ Γp)) t
    in box-GlobalFibered ts'
  transl-Term-▲ Γ Γp (letmod-＠ {U = i} {A = A} (＠ₛ U) ν t s) = {!!}
    -- let t' = transl-Term-◯ _ (isGood:splits (stepRes _ Γp)) (splits-path t)
    --     t'' = cong-GlobalFibered (lemma:transl,restr {μ = ν}) t'
    --     s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))
    -- in letin-GlobalFibered (multibox t'') s'
    -- let t' = transl-Term-◯ _ ? (splits-path t)
    --     t'' = cong-GlobalFibered ? t'
    --     s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))

{-
    let t' : transl-Ctx (Γ ∙! ＠ₛ _ ∙!* split-Min𝔐TT ν) _ ⊢ ⦋ A ⦌-Type ＠ U GlobalFibered[ _ ]
        t' = transl-Term-◯ _ (stepsRes _ (stepRes _ Γp)) t

        s' = transl-Term-▲ _ ((stepVar Γp)) s

        t'' : addRestr ν (transl-Ctx Γ Γp , i) ⊢ ⦋ A ⦌-Type ＠ U GlobalFibered[ _ ]
        t'' = cong-GlobalFibered commute-transl,addRestr t'

        s'' = cong-GlobalFibered (cong-Ctx,Var (eval-F-type-right {ν = ν} {X = ⦋ A ⦌-Type ＠ U})) s'

        res : (transl-Ctx Γ Γp) ⊢ _ GlobalFibered[ _ ]
        res = letin-GlobalFibered (multibox t'') s''

    in res
    -}
  transl-Term-▲ Γ Γp (letmod-＠ []ₛ id' t s) =
    let
        t'' = transl-Term-▲ _ Γp t
        s' = transl-Term-▲ _ ((stepVar Γp)) s
    in letin-GlobalFibered t'' s'
  transl-Term-▲ Γ Γp (letmod-＠ {U = i} {A = A} []ₛ (`＠` U ⨾ ν) t s) = {!!}
  {-
    let
        t'' = transl-Term-▲ _ ((stepsRes _ (stepRes _ Γp))) t

        t''' : addRestr (ν) (transl-Ctx Γ Γp , i) ⊢ (◻ ⦋ A ⦌-Type) ＠ U GlobalFibered[ _ ]
        t''' = cong-GlobalFibered commute-transl,addRestr t''
        s' = transl-Term-▲ _ ((stepVar Γp)) s
        s'' = cong-GlobalFibered (cong-Ctx,Var ((eval-F-type-right {ν = ν} {X = ◻ ⦋ A ⦌-Type ＠ U}))) s'

    in letin-GlobalFibered (multibox t''') s''
  -}

  transl-Term-▲ Γ Γp (pure t) = pure-＠-GlobalFibered (transl-Term-▲ Γ Γp t)
  transl-Term-▲ Γ Γp (seq-＠ t s) =
    let t' = transl-Term-▲ Γ Γp t
        s' = transl-Term-▲ _ (stepVar Γp) s
    in seq-＠-GlobalFibered t' s'
  transl-Term-▲ Γ Γp (lam-＠ t) =
      let -- t' = com-restr-single t
          rest' = transl-Term-▲ _ (stepVar Γp) t
      in commute⁻¹-＠-Exp _ (lam-GlobalFibered rest')
  transl-Term-▲ Γ Γp (app t s) =
    let t' = transl-Term-▲ Γ Γp t
        s' = transl-Term-▲ Γ Γp s
    in app-GlobalFibered (commute-＠-Exp _ t') s'
  transl-Term-▲ Γ Γp (left t) = left-＠-GlobalFibered (transl-Term-▲ Γ Γp t)
  transl-Term-▲ Γ Γp (right t) = right-＠-GlobalFibered (transl-Term-▲ Γ Γp t)
  transl-Term-▲ Γ Γp (either-＠ t s u) =
    let t' = transl-Term-▲ Γ Γp t
        s' = transl-Term-▲ _ (stepVar Γp) s
        u' = transl-Term-▲ _ (stepVar Γp) u
    in either-＠-GlobalFibered t' s' u'
  transl-Term-▲ Γ Γp [] = []-＠-GlobalFibered
  transl-Term-▲ Γ Γp (t ∷ s) =
    let t' = transl-Term-▲ Γ Γp t
        s' = transl-Term-▲ Γ Γp s
    in t' ∷ s' -＠-GlobalFibered
  transl-Term-▲ Γ Γp (rec-Lst-＠ t s u) =
    let t' = transl-Term-▲ Γ Γp t
        s' = transl-Term-▲ _ Γp s
        u' = transl-Term-▲ _ (stepVar (stepVar Γp)) u
    in rec-Lst-＠-GlobalFibered t' s' u'


  transl-Term-◯ Γ Γp (var {b = ▲ _} x α αp) = ⊥-elim (local-var-impossible Γp x)
  transl-Term-◯ Γ Γp (var {b = ◯} {μ = μ} x α αp) =
    incl (λ p x₁ Xp Γp₁ → var (transl-Var-◯ {ν = id'} Γ Γp x (transToSublist₁ α {!!}) Γp₁ Xp))
  transl-Term-◯ Γ Γp tt = tt-GlobalFibered
  transl-Term-◯ Γ Γp (mod (＠ₛ U) t) = transl-Term-▲ Γ Γp t
  transl-Term-◯ Γ Γp (letmod (＠ₛ U) ν t s) = {!!}
  {-
    let t' = transl-Term-◯ _ (stepsRes _ Γp) t

        s' = transl-Term-◯ _ ((stepVar Γp)) s

        t'' = cong-GlobalFibered (commute-transl,addRestr-2 {ν = ν}) t'

        res : (transl-Ctx Γ Γp) ⊢ _ GlobalFibered[ _ ]
        res = letin-GlobalFibered (multibox' t'') s'

    in res
  -}
  transl-Term-◯ Γ Γp (letmod []ₛ (`＠` i ⨾ ν) t s) = {!!}
  {-
    let
        t'' = transl-Term-▲ _ ((stepsRes _ (Γp))) t
        t''' = cong-GlobalFibered (commute-transl,addRestr-2 {ν = ν}) t''
        s' = transl-Term-◯ _ ((stepVar Γp)) s
    in letin-GlobalFibered (multibox' t''') s'
  -}
  transl-Term-◯ Γ Γp (broadcast t) =
      let t' = transl-Term-◯ _ Γp t
      in broadcast-GlobalFibered t'
  transl-Term-◯ Γ Γp (pure t) = pure-GlobalFibered (transl-Term-◯ Γ Γp t)
  transl-Term-◯ Γ Γp (seq t s) =
    let t' = transl-Term-◯ Γ Γp t
        s' = transl-Term-◯ _ (stepVar Γp) s
    in seq-GlobalFibered t' s'
  transl-Term-◯ Γ Γp (lam t) =
    let t' = transl-Term-◯ _ (stepVar Γp) t
    in lam-GlobalFibered t'
  transl-Term-◯ Γ Γp (app t s) =
    let t' = transl-Term-◯ Γ Γp t
        s' = transl-Term-◯ _ Γp s
    in app-GlobalFibered t' s'
  transl-Term-◯ Γ Γp (left t) =
    let t' = transl-Term-◯ Γ Γp t
    in left-GlobalFibered t'
  transl-Term-◯ Γ Γp (right t) =
    let t' = transl-Term-◯ Γ Γp t
    in right-GlobalFibered t'
  transl-Term-◯ Γ Γp (either t s u) =
    let t' = transl-Term-◯ Γ Γp t
        s' = transl-Term-◯ _ (stepVar Γp) s
        u' = transl-Term-◯ _ (stepVar Γp) u
    in either-GlobalFibered t' s' u'
  transl-Term-◯ Γ Γp [] = []-GlobalFibered
  transl-Term-◯ Γ Γp (t ∷ s) =
    let t' = transl-Term-◯ Γ Γp t
        s' = transl-Term-◯ _ Γp s
    in _∷_-GlobalFibered t' s'
  transl-Term-◯ Γ Γp (rec-Lst t s u) =
    let t' = transl-Term-◯ Γ Γp t
        s' = transl-Term-◯ Γ Γp s
        u' = transl-Term-◯ _ (stepVar (stepVar Γp)) u
    in rec-Lst-GlobalFibered t' s' u'

{-

{-
{-
  -}
  {-

{-
  ⟪𝔉₃∣_Term⟫ : {a : Param Super} -> {Γ : Ctx a of Super} -> {X : Type a of Super}
               -> Γ ⊢ X at a of Super
               -> ⟪𝔉₃∣ Γ Ctx⟫ ⊢ ⟪𝔉₃∣ X Type⟫ at tt of This
  ⟪𝔉₃∣_Term⟫ {a = ▲ U} {Γ = (Γ ∙! ＠ₛ U) , stepRes (`＠` U) Γp} {X} t = transl-Term-▲ Γ Γp t
  ⟪𝔉₃∣_Term⟫ {a = ◯} {Γ = Γ , Γp} {X} t = transl-Term-◯ Γ Γp t

  -- End Terms
  --------------------------------------------------------------------

  module _ {a : Param Super} where


  run-𝔉₃ : ∀{a : Param Super} -> (pa : SubParam Super a) -> Hom-STT (Super at a) (This at tt)
  run-𝔉₃ pa = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₃∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₃∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₃∣_Term⟫
    }


-}

{-
instance
  isReduction:F₃ : isParamSTTHom (Chor𝔓roc 𝑗) (Chor𝔐TT _) F₃
  isReduction:F₃ = record
    { param = par-𝔉₃
    ; runAt = run-𝔉₃
    }

module _ {𝑗} where macro 𝔉₃ = #structureOn (F₃ {𝑗 = 𝑗})
-}

-}
-}
-}
