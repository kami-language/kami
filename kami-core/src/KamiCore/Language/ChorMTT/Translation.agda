

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Language.ChorMTT.Translation where

open import Data.List using (drop)

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import Agora.TypeTheory.STT.Definition
open import Agora.TypeTheory.ParamSTT.Definition

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
-- open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)

open import KamiCore.Language.MinMTT.Definition
open import KamiCore.Language.ChorMTT.Definition



F₂ : Chor𝔐TT 𝑗 -> Min𝔐TT _
F₂ This = Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private].Super This

module _ (This : Chor𝔐TT 𝑗) where
  -- open Chor𝔐TT/Definition This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Private] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Param] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Ctx] This
  open Chor𝔐TT/Definition.[Chor𝔐TT/Definition::Term] This

  -- open Min𝔐TT/Definition Super
  open Min𝔐TT/Definition.[Min𝔐TT/Definition::Private] Super using (𝓂)
  open Min𝔐TT/Definition.[Min𝔐TT/Definition::Ctx] Super -- renaming (⊢Ctx to Min𝔐TT⊢Ctx)
  open Min𝔐TT/Definition.[Min𝔐TT/Definition::Type] Super
  open Min𝔐TT/Definition.[Min𝔐TT/Definition::Term] Super renaming (_⊢_ to _Min𝔐TT⊢_)


  par-𝔉₂ : Param Super -> Param This
  par-𝔉₂ (x , a) = a

  --------------------------------------------------------------------
  -- Types

  ⟪𝔉₂∣_Type⟫ : {a : Param This} -> Type (◯ , a) of Super -> Type (a) of This
  ⟪𝔉₂∣_Type⟫ X = X

  -- End Types
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Contexts

  pattern []ₛ = (`[]` ⨾ id' , incl `[]`)
  pattern ＠ₛ U  = (`＠` U ⨾ id' , incl (`＠` _))

  transl-Ctx : {a : 𝓂} -> ⊢Ctx {◯} a -> ∑ λ (Γ : ⊢Ctx {◯} ◯) -> isCtx₂ Γ
  transl-Ctx {a = ◯} ε = ε , ε
  transl-Ctx {a = ◯} (Γ ∙⟮ A ∣ μ ⟯) =
    let Γ' , Γ'p = transl-Ctx Γ
    in Γ' ∙⟮ A ∣ μ ⟯ , stepVar Γ'p
  transl-Ctx {a = ◯} (Γ ∙! (`[]` {U = U} ⨾ id' , incl `[]`)) =
    let Γ' , Γ'p = transl-Ctx Γ
    in Γ' ∙! ＠ₛ U ∙! []ₛ , stepRes _ (stepRes _ Γ'p)
  transl-Ctx {a = ▲ U} (Γ ∙⟮ A ∣ μ ⟯) =
    let Γ' , Γ'p = transl-Ctx Γ
    in Γ' ∙⟮ A ∣ μ ◆' (`＠` U ⨾ id') ⟯ , stepVar Γ'p
  transl-Ctx {a = ▲ u} (Γ ∙! ＠ₛ U) =
    let Γ' , Γ'p = transl-Ctx Γ
    in Γ' , Γ'p

  ⟪𝔉₂∣_Ctx⟫ : {a : 𝓂} -> ⊢Ctx {◯} a -> ∑ λ (Γ : ⊢Ctx {◯} a) -> isCtx₂ Γ
  ⟪𝔉₂∣_Ctx⟫ {a = ◯} Γ = transl-Ctx Γ
  ⟪𝔉₂∣_Ctx⟫ {a = ▲ U} Γ =
    let Γ' , Γ'p = transl-Ctx Γ
    in Γ' ∙! ＠ₛ U , stepRes _ Γ'p


  -- End Contexts
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- Terms

  com-restr-single : ∀{x : BaseModeHom-PolySR a b} -> ∀{xp} -> {A : ⊢Type c}
                    -> {B : ⊢Type a}
                    -> (Γ ∙! ((x ⨾ id') , xp)) ∙⟮ A ∣ μ ⟯ ⊢ B
                    -> Γ ∙⟮ A ∣ μ ◆ (x ⨾ id') ⟯ ∙! ((x ⨾ id') , xp) ⊢ B
  com-restr-single = {!!}

  com⁻¹-restr-single : ∀{x : BaseModeHom-PolySR a b} -> ∀{xp} -> {A : ⊢Type c}
                    -> {B : ⊢Type a}
                    -> Γ ∙⟮ A ∣ μ ◆ (x ⨾ id') ⟯ ∙! ((x ⨾ id') , xp) ⊢ B
                    -> (Γ ∙! ((x ⨾ id') , xp)) ∙⟮ A ∣ μ ⟯ ⊢ B
  com⁻¹-restr-single = {!!}

  transl-Term-▲ : ∀{U} -> {Γ : ⊢Ctx {◯} (▲ U)} -> {X : ⊢Type (▲ U)}
               -> Γ ⊢ X at (◯ , ▲ U) of Super
               -> ⟪𝔉₂∣ Γ Ctx⟫ ⊢ ⟪𝔉₂∣ X Type⟫ at ▲ U of This

  transl-Term-◯ : {Γ : ⊢Ctx {◯} ◯} -> {X : ⊢Type (◯)}
               -> Γ ⊢ X at (◯ , ◯) of Super
               -> ⟪𝔉₂∣ Γ Ctx⟫ ⊢ ⟪𝔉₂∣ X Type⟫ at ◯ of This


  transl-Term-▲ (var x α x₁) = {!!}
  transl-Term-▲ tt = tt
  transl-Term-▲ (mod ([]ₛ) t) = mod ([]ₛ) (transl-Term-◯ t)
  transl-Term-▲ {U = U} {Γ = Γ} {X = X} (letmod {n = ◯} {A = A} {μ = μ} ν t s) =
    let t' : fst (transl-Ctx (Γ ∙!* split-Min𝔐TT ν)) ⊢ ⟨ A ∣ μ ⟩
        t' = transl-Term-◯ t

        t'' : fst (transl-Ctx Γ) ∙! ＠ₛ U ∙!* split-Min𝔐TT ν ⊢ ⟨ A ∣ μ ⟩
        t'' = {!!}

        s' = transl-Term-▲ s

    in letmod (ν) t'' (com⁻¹-restr-single s')
  transl-Term-▲ {U = U} {Γ = Γ}(letmod {n = ▲ V} {A = A} {μ = μ} ν t s) =
    let t' : fst (transl-Ctx (Γ ∙!* split-Min𝔐TT ν)) ∙! ＠ₛ V ⊢ ⟨ A ∣ μ ⟩
        t' = transl-Term-▲ t

        t'' : ((fst (transl-Ctx Γ) ∙! ＠ₛ U) ∙!* split-Min𝔐TT ν) ⊢ ⟨ A ∣ μ ⟩
        t'' = {!!}

        s' = transl-Term-▲ s

    in letmod ν t'' (com⁻¹-restr-single s')
  transl-Term-▲ (pure t) = pure (transl-Term-▲ t)
  transl-Term-▲ (seq t s) =
    let s' = (transl-Term-▲ s)
        s'' = (com⁻¹-restr-single {μ = id'} s')
    in seq (transl-Term-▲ t) s''
  transl-Term-▲ (lam t) =
    let t' = transl-Term-▲ t
    in lam (com⁻¹-restr-single {μ = id'} t')
  transl-Term-▲ (app t s) = app (transl-Term-▲ t) (transl-Term-▲ s)
  transl-Term-▲ (left t) = left (transl-Term-▲ t)
  transl-Term-▲ (right t) = right (transl-Term-▲ t)
  transl-Term-▲ (either t t₁ t₂) =
    let t₁' = com⁻¹-restr-single {μ = id'} (transl-Term-▲ t₁)
        t₂' = com⁻¹-restr-single {μ = id'} (transl-Term-▲ t₂)
    in either (transl-Term-▲ t) t₁' t₂'
  transl-Term-▲ [] = []
  transl-Term-▲ (t ∷ t₁) = (transl-Term-▲ t) ∷ (transl-Term-▲ t₁)
  transl-Term-▲ (rec-Lst t t₁ t₂) = {!!} -- TODO: This requires `com⁻¹-restr-single` to work not only on the top variable, but also below.

  transl-Term-◯ (var x α x₁) = {!!}
  transl-Term-◯ tt = tt
  transl-Term-◯ (mod (＠ₛ U) t) = mod (＠ₛ U) (transl-Term-▲ t)
  transl-Term-◯ {Γ = Γ} {X = X} (letmod {n = ◯} {A = A} {μ = μ} ν t s) =
    let t' = transl-Term-◯ t

        t'' : fst (transl-Ctx Γ) ∙!* split-Min𝔐TT ν ⊢ ⟨ A ∣ μ ⟩
        t'' = {!!}

        s' = transl-Term-◯ s

    in letmod ν t'' s'
  transl-Term-◯ {Γ = Γ}(letmod {n = ▲ V} {A = A} {μ = μ} ν t s) =
    let t' : fst (transl-Ctx (Γ ∙!* split-Min𝔐TT ν)) ∙! ＠ₛ V ⊢ ⟨ A ∣ μ ⟩
        t' = transl-Term-▲ t

        t'' : (fst (transl-Ctx Γ) ∙!* split-Min𝔐TT ν) ⊢ ⟨ A ∣ μ ⟩
        t'' = {!!}

        s' = transl-Term-◯ s

    in letmod ν t'' s'
  transl-Term-◯ (pure t) = pure (transl-Term-◯ t)
  transl-Term-◯ (seq t t₁) = seq (transl-Term-◯ t) (transl-Term-◯ t₁)
  transl-Term-◯ (lam t) = lam (transl-Term-◯ t)
  transl-Term-◯ (app t t₁) = app ((transl-Term-◯ t)) ((transl-Term-◯ t₁))
  transl-Term-◯ (left t) = left (transl-Term-◯ t)
  transl-Term-◯ (right t) = right (transl-Term-◯ t)
  transl-Term-◯ (either t t₁ t₂) = either (transl-Term-◯ t) (transl-Term-◯ t₁) (transl-Term-◯ t₂)
  transl-Term-◯ [] = []
  transl-Term-◯ (t ∷ t₁) = (transl-Term-◯ t) ∷ (transl-Term-◯ t₁)
  transl-Term-◯ (rec-Lst t t₁ t₂) = rec-Lst (transl-Term-◯ t) (transl-Term-◯ t₁) (transl-Term-◯ t₂)

  ⟪𝔉₂∣_Term⟫ : {a : Param This} -> {Γ : Ctx (◯ , a) of Super} -> {X : Type (◯ , a) of Super}
               -> Γ ⊢ X at (◯ , a) of Super
               -> ⟪𝔉₂∣ Γ Ctx⟫ ⊢ ⟪𝔉₂∣ X Type⟫ at a of This
  ⟪𝔉₂∣_Term⟫ {a = ◯} = transl-Term-◯
  ⟪𝔉₂∣_Term⟫ {a = ▲ U} = transl-Term-▲

  -- End Terms
  --------------------------------------------------------------------

  run-𝔉₂ : ∀{a : Param Super} -> (pa : SubParam Super a) -> Hom-STT (Super at a) (This at (par-𝔉₂ a))
  run-𝔉₂ refl-≡ = record
    { ⟪_∣_Ctx⟫ = ⟪𝔉₂∣_Ctx⟫
    ; ⟪_∣_Type⟫ = ⟪𝔉₂∣_Type⟫
    ; ⟪_∣_Term⟫ = ⟪𝔉₂∣_Term⟫
    }

instance
  isReduction:F₂ : isParamSTTHom (Chor𝔐TT 𝑗) (Min𝔐TT _) F₂
  isReduction:F₂ = record
    { param = par-𝔉₂
    ; runAt = run-𝔉₂
    }

module _ {𝑗} where macro 𝔉₂ = #structureOn (F₂ {𝑗 = 𝑗})

{-
-}
