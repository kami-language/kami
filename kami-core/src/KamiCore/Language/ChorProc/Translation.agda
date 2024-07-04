

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

  transl-Ctx' : (Γ : Chor𝔐TT⊢Ctx {◯} a) -> isCtx₂ Γ -> ⊢Ctx
  transl-Ctx' Γ Γp = forget (transl-Ctx Γ Γp)

  ⟪𝔉₃∣_Ctx⟫ : Ctx a of Super -> Ctx tt of This
  ⟪𝔉₃∣_Ctx⟫ (Γ , Γp) = forget (transl-Ctx Γ Γp)

  -- End Contexts
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Context commutation proofs


  cong-,[] : ∀{Γ Δ : TargetCtx ▲} -> Γ ≡ Δ -> fst Γ ,[ snd Γ ] ≡ fst Δ ,[ snd Δ ]
  cong-,[] refl-≡ = refl-≡


  commute-transl,addRestr : {ν : a ⟶ ▲ U} -> ∀{Γ Γp} -> transl-Ctx
     (Γ ∙! ＠ₛ U ∙!* split-Min𝔐TT ν) (stepsRes _ (stepRes _ Γp))
     ≡ addRestr ν (transl-Ctx Γ Γp , U)
  commute-transl,addRestr {ν = id'} = refl-≡
  commute-transl,addRestr {ν = `＠` U ⨾ ν} = cong-≡ (_, U) (commute-transl,addRestr {ν = ν})
  commute-transl,addRestr {ν = `[]` ⨾ ν} = cong-,[] (commute-transl,addRestr {ν = ν})

  commute-transl,addRestr-2 : ∀{ν : a ⟶ ◯} -> ∀{Γ Γp} -> transl-Ctx
     (Γ ∙!* split-Min𝔐TT ν) (stepsRes _ Γp)
     ≡ addRestr ν (transl-Ctx Γ Γp)
  commute-transl,addRestr-2 {ν = id'} = refl-≡
  commute-transl,addRestr-2 {ν = `＠` U ⨾ ν} = cong-≡ (_, U) (commute-transl,addRestr-2 {ν = ν})
  commute-transl,addRestr-2 {ν = `[]` ⨾ ν} = cong-,[] (commute-transl,addRestr-2 {ν = ν})


  -- End Context commutation proofs
  --------------------------------------------------------------------


  --------------------------------------------------------------------
  -- Variables


  local-var-impossible : ∀{b c A} {Γ : Chor𝔐TT⊢Ctx c} -> (Γp : isCtx₂ Γ) -> {μ : b ⟶ ▲ U} {η : c ⟶ ▲ U} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> 𝟘-𝒰
  local-var-impossible (stepRes _ Γp) (suc! v) = local-var-impossible Γp v
  local-var-impossible (stepVar Γp) (suc v) = local-var-impossible Γp v


{-
  transl-Var-▲ : (Γ : Chor𝔐TT⊢Ctx ◯) -> ∀ Γp ->  ∀{U V} -> {A : Chor𝔐TT⊢Type (▲ U)}
              -> Γ ⊢Var⟮ A ∣ (`＠` U ⨾ μ) ⇒ (η) ⟯
              -> rev (transl-Mod3 (`[]` ⨾ `＠` U ⨾ μ)) ≼' rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ (ν ◆' η)))
              -> ∀{p Δ B}
              -> transl-Ctx' Γ Γp ∣ cons (postpend (rev' (transl-Mod3 (ν))) p) ↦ Δ Ctx
              -> π ⦋ A ⦌-Type ＠ V ∣ p , [] ↦ B Type
              -> Δ ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ (`＠` U ⨾ μ) ⟯) (stepVar Γp) {U = U} {V} {A = A} zero μ≼ν {p = p} {Δ = Δ , _} {B = B} (Γpp , x₁) Xp =
    let
        YY : (Δ , F2-Type (rev (transl-Mod3 (μ))) (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
        YY = mkVar-▲ {U = U} {V = V} {ps = (rev (transl-Mod3 (μ)))} {qs = (rev' (transl-Mod3 (ν)))} (μ≼ν ◆-≼'≡ (sym-≡ (rev≡rev' (transl-Mod3 (`[]` ⨾ `＠` V ⨾ ν))) ∙-≡ cong-≡ (_++-List V ∷ []) (rev≡rev' (transl-Mod3 ν)) )) Xp
-- (transl-Mod3 (`[]` ⨾ `＠` V ⨾ ν))

        -- mkVar {ps = (rev (transl-Mod3 μ))} {qs = (rev' (transl-Mod3 (`[]` ⨾ ν)))} μ≼ν Xp

        ZZ : (Δ , F-Type μ (⦋ x ⦌-Type ＠ U)) ⊢Var B GlobalFiber[ cons (postpend (rev' (transl-Mod3 (ν))) p) ]
        ZZ = transp-Ctx-Var (cong-Ctx,Var (sym-≡ (F-prop {μ = μ} {X = (⦋ x ⦌-Type ＠ U)}))) YY

    in updateVar x₁ ZZ
  transl-Var-▲ {ν = ν} (Γ ∙! ＠ₛ U ∙! []ₛ) (stepRes `[]` (stepRes x Γp)) (suc! (suc! v)) PP {p = p} {Δ = Δ ,[ _ ]} {B = B} (stepRes Γpp) Xp = {!!}
  transl-Var-▲ {ν = ν} (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) (suc v) PP (Γpp , x₁) Xp =
    let res = transl-Var-▲ {ν = ν} Γ Γp v PP Γpp Xp
    in suc res

-}

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

    in updateVar x₁ ZZ
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
        Γpp' = transp-≡ (cong-≡ (λ ξ -> transl-Ctx' Γ Γp ∣ ξ ↦ Δ Ctx) {!!}) Γpp

        result = transl-Var-◯ {ν = ν ◆ (`[]` ⨾ `＠` U ⨾ id')} Γ Γp v PP Γpp' Xp


        result' : Δ ⊢Var B GlobalFiber[ U ∷ cons (postpend (rev' (transl-Mod3 ν)) p) ]
        result' = transp-≡ (cong-≡ (λ ξ -> Δ ⊢Var B GlobalFiber[ ξ ]) P1) result

    in res result'

  -- End Variables
  --------------------------------------------------------------------

{-


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
    incl (λ p x₁ Xp Γp₁ → (let XX = (transl-Var-▲ {ν = id'} Γ Γp x {!!} Γp₁ Xp) in var XX))

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
