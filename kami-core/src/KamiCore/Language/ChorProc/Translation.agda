

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
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding (Mode)
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category

open import KamiCore.Language.ChorMTT.Definition
open import KamiCore.Language.ChorMTT.Properties
open import KamiCore.Language.ChorProc.Definition
open import KamiCore.Language.ChorProc.Properties




F₃ : Chor𝔓roc 𝑗 -> Chor𝔐TT _
F₃ This = Chor𝔓roc/Definition.Super This


module _ (This : Chor𝔓roc 𝑗) where
  open Chor𝔓roc/Definition This
  open [Chor𝔓roc/Definition::Param]
  open [Chor𝔓roc/Definition::Type]
  open [Chor𝔓roc/Definition::Ctx]
  open [Chor𝔓roc/Definition::Term]
  open Chor𝔓roc/Properties This

  open Chor𝔐TT/Definition Super
  open [Chor𝔐TT/Definition::Type] hiding (⊢Type)
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




  --------------------------------------------------------------------
  -- Types


  ⦋_⦌-Type : Type a of Super -> ⊢Type ⟦ a ⟧-Mode
  ⦋ ⟨ X ∣ μ ⟩ ⦌-Type = F-Type (fst μ) ⦋ X ⦌-Type
  ⦋ Unit ⦌-Type = Unit
  ⦋ Tr X ⦌-Type = Tr ⦋ X ⦌-Type
  ⦋ X ⇒ Y ⦌-Type = ⦋ X ⦌-Type ⇒ ⦋ Y ⦌-Type
  ⦋ Either X Y ⦌-Type = Either ⦋ X ⦌-Type ⦋ Y ⦌-Type
  ⦋ Lst X ⦌-Type = Lst ⦋ X ⦌-Type

  ⟪𝔉₃∣_Type⟫ : {a : Param Super} -> Type a of Super -> Type tt of This
  ⟪𝔉₃∣_Type⟫ {a = ▲ x} X = ⦋ X ⦌-Type ＠ x
  ⟪𝔉₃∣_Type⟫ {a = ◯} X = ⦋ X ⦌-Type

  -- End Types
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Types commutation proofs
  -- End Types commutation proofs
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Contexts

  transl-Ctx : (Γ : Chor𝔐TT⊢Ctx {◯} a) -> isCtx₂ Γ -> TargetCtx ⟦ a ⟧-Mode
  transl-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl-Ctx (_∙!_ Γ μ) (stepRes _ Γp) = addRestr (fst μ) (transl-Ctx Γ Γp)
  transl-Ctx ε Γp = ε

  ⟪𝔉₃∣_Ctx⟫ : Ctx a of Super -> Ctx tt of This
  ⟪𝔉₃∣_Ctx⟫ (Γ , Γp) = forget (transl-Ctx Γ Γp)

  -- End Contexts
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Context commutation proofs


  commute-transl,addRestr : ∀{Γ Γp Γp'} -> transl-Ctx
     (Γ ∙! ＠ₛ U ∙!* split-Min𝔐TT ν) Γp'
     ≡ addRestr ν (transl-Ctx Γ Γp , U)
  commute-transl,addRestr = {!!}

  commute-transl,addRestr-2 : ∀{Γ Γp Γp'} -> transl-Ctx
     (Γ ∙!* split-Min𝔐TT ν) Γp'
     ≡ addRestr ν (transl-Ctx Γ Γp)
  commute-transl,addRestr-2 = {!!}

  -- End Context commutation proofs
  --------------------------------------------------------------------


  --------------------------------------------------------------------
  -- Terms
  transl-Term-▲ : ∀{ps} {i : ⟨ P ⟩} -> (Γ : Chor𝔐TT⊢Ctx {◯} ◯) -> (Γp : isCtx₂ Γ)
            -> ∀{A} -> Γ ∙! (＠ₛ i) Chor𝔐TT⊢ A
            -> transl-Ctx Γ Γp  ⊢ (⦋ A ⦌-Type ＠ i) GlobalFibered[ ps ]
  transl-Term-▲ = {!!}

  transl-Term-◯ : ∀{ps} -> (Γ : Chor𝔐TT⊢Ctx {◯} ◯) -> (Γp : isCtx₂ Γ)
            -> ∀{A} -> Γ Chor𝔐TT⊢ A
            -> transl-Ctx Γ Γp  ⊢ ⦋ A ⦌-Type GlobalFibered[ ps ]


  {-
  transl-Term-▲ Γ Γp (var x α) = {!!}
  transl-Term-▲ Γ Γp tt = tt-▲-GlobalFibered
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
  -}

  transl-Term-◯ Γ Γp (var x α) = {!!}
  transl-Term-◯ Γ Γp tt = tt-GlobalFibered
  transl-Term-◯ Γ Γp (mod (＠ₛ U) t) = transl-Term-▲ Γ Γp t
  transl-Term-◯ Γ Γp (letmod (＠ₛ U) ν t s) =
    let t' = transl-Term-◯ _ (stepsRes _ Γp) t

        s' = transl-Term-◯ _ ((stepVar Γp)) s

        t'' = cong-GlobalFibered (commute-transl,addRestr-2 {ν = ν}) t'

        res : (transl-Ctx Γ Γp) ⊢ _ GlobalFibered[ _ ]
        res = letin-GlobalFibered (multibox' t'') s'

    in res
  transl-Term-◯ Γ Γp (letmod []ₛ (`＠` i ⨾ ν) t s) =
    let
        t'' = transl-Term-▲ _ ((stepsRes _ (Γp))) t
        t''' = cong-GlobalFibered (commute-transl,addRestr-2 {ν = ν}) t''
        s' = transl-Term-◯ _ ((stepVar Γp)) s
    in letin-GlobalFibered (multibox' t''') s'
  transl-Term-◯ Γ Γp (pure t) = {!!}
  transl-Term-◯ Γ Γp (seq t t₁) = {!!}
  transl-Term-◯ Γ Γp (lam t) = {!!}
  transl-Term-◯ Γ Γp (app t t₁) = {!!}
  transl-Term-◯ Γ Γp (left t) = {!!}
  transl-Term-◯ Γ Γp (right t) = {!!}
  transl-Term-◯ Γ Γp (either t t₁ t₂) = {!!}
  transl-Term-◯ Γ Γp [] = {!!}
  transl-Term-◯ Γ Γp (t ∷ t₁) = {!!}
  transl-Term-◯ Γ Γp (rec-Lst t t₁ t₂) = {!!}


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

{-
-}
