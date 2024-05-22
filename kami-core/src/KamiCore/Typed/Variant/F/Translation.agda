
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiCore.Typed.Variant.F.Translation where

open import Agora.Conventions hiding (m ; n ; k ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Category.Std.Category.Definition
open import Agora.Category.Std.2Category.Definition
open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Data.UniqueSortedList.Definition
open import KamiTheory.Data.List.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Instance.2Category


open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition renaming (_◆_ to _◆'_ ; id to id')

open import KamiTheory.Order.StrictOrder.Base
open import KamiTheory.Basics hiding (_⋆_)



module Translation (n : ℕ) where
-- (P : Preorder 𝑖) {{_ : hasDecidableEquality ⟨ P ⟩}} {{_ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)}} where

  P : Preorder _
  P = 𝒫ᶠⁱⁿ (𝔽 n)

  instance
    hasDecidableEquality:P : hasDecidableEquality ⟨ P ⟩
    hasDecidableEquality:P = {!!}

  instance
    isProp:≤ : ∀{a b : ⟨ P ⟩} -> isProp (a ≤ b)
    isProp:≤ = {!!}

  -- Getting the mode system
  import KamiTheory.Main.Generic.ModeSystem.2Graph.Example as 2GraphExample
  import KamiTheory.Main.Generic.ModeSystem.2Cell.Example as 2CellExample
  open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
  open SendReceiveNarrow-ModeSystem P {{it}} {{it}}
  open 2GraphExample.SendReceiveNarrow-2Graph P
  -- open 2CellExample.SendReceiveNarrow-2Cells P {{it}} {{it}}


  -- Instantiating MTT with the 2category generated from the modesystem
  open import KamiCore.Typed.Variant.F.Definition3

  instance
    Param : MTTꟳ _
    Param = record
      { 𝓂 = Mode SRN-ModeSystem
      ; isCategory:𝓂 = isCategory:byModeSystem SRN-ModeSystem
      ; is2Category:𝓂 = is2Category:byModeSystem SRN-ModeSystem
      }


  open Definition-MTTꟳ {{Param}}
    renaming (ModeHom to ModeHom' ; _⊢_ to _⊢'_)

  instance
    isCategoryData:ModeHom : isCategoryData (Mode SRN-ModeSystem) ModeHom'
    isCategoryData:ModeHom = HomData {{isCategory:𝓂 {{Param}}}}

  instance
    isCategory:ModeHom : isCategory (Mode SRN-ModeSystem)
    isCategory:ModeHom = record { Hom = ModeHom' }

  instance
    is2Category:ModeHom : is2Category ′(Mode SRN-ModeSystem)′
    is2Category:ModeHom = is2Category:𝓂 {{Param}}


  -- Instantiating the target language with the preorder
  open import KamiCore.Typed.Variant.F.Model7

  ρ : isProcessSet _
  ρ = record { Proc = 𝔽 n }

  open IR {{ρ}}
    renaming (Ctx to Ctx' ; Mode to Mode')


  private variable
    a b c : Mode SRN-ModeSystem
    μ ν η ω : ModeHom' a b



  --------------------------------------------------
  -- Translating MTT terms into a form where the
  -- contexts only have single restrictions form.
  data isCtx₁ : Ctx a -> 𝒰₀ where
    ε : isCtx₁ {a = a} ε
    stepVar : {Γ : Ctx b} -> isCtx₁ Γ -> {A : ⊢Type a} -> {μ : a ⟶ b} -> isCtx₁ (Γ ∙⟮ A ∣ μ ⟯)
    stepRes : {Γ : Ctx b} -> isCtx₁ Γ -> {μ : BaseModeHom-SRN a b} -> isCtx₁ (Γ ∙! (μ ⨾ id))


  addRes : (μ : a ⟶ b) -> ∑ isCtx₁ {a = b} -> ∑ isCtx₁ {a = a}
  addRes id' Γ = Γ
  addRes (x ⨾ μ) Γ =
    let Γ' , Γ'p = addRes μ Γ
    in Γ' ∙! (x ⨾ id') , stepRes Γ'p

  toCtx₁ : Ctx a -> ∑ isCtx₁ {a = a}
  toCtx₁ ε = ε , ε
  toCtx₁ (Γ ∙⟮ x ∣ x₁ ⟯) =
    let Γ , Γp = toCtx₁ Γ
    in Γ ∙⟮ x ∣ x₁ ⟯ , stepVar Γp
  toCtx₁ (Γ ∙! μ) = addRes μ (toCtx₁ Γ)

  -- to₁-Var : ∀{Γ : Ctx a} {A : ⊢Type a} -> Γ ⊢ A -> fst (toCtx₁ Γ) ⊢ 

  --------------------------------------------------
  -- Translating MTT terms into a form where the
  -- contexts only have {＠j}{◻} form.



  --------------------------------------------------
  -- An MTT version which has only single 
  module _ where
    private variable
      Γ : Ctx a
      A B : ⊢Type a

    data _⊢_ : Ctx a -> ⊢Type a -> 𝒰₀ where
      var : ∀{μ : _ ⟶ b} -> Γ ⊢Var⟮ A ∣ μ ⇒ η ⟯ -> (α : μ ⟹ η) -> Γ ⊢ A
      tt : Γ ⊢ Unit

      -- modalities
      mod : ∀ μ -> Γ ∙! (μ ⨾ id') ⊢ A -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
      letmod : ∀(μ : a ⟶ b) -> (ν : b ⟶ c)
            -> Γ ∙! ν ⊢ ⟨ A ∣ μ ⟩
            -> Γ ∙⟮ A ∣ μ ◆ ν ⟯ ⊢ B
            -> Γ ⊢ B

      letmod' : ∀(μ : BaseModeHom-SRN a b)
            -> Γ ⊢ ⟨ A ∣ μ ⨾ id' ⟩
            -> Γ ∙⟮ A ∣ μ ⨾ id' ⟯ ⊢ B
            -> Γ ⊢ B

      -- explicit transformations
      trans : ∀ {μ ν : a ⟶ b} -> μ ⟹ ν -> Γ ⊢ ⟨ A ∣ μ ⟩ -> Γ ⊢ Tr ⟨ A ∣ ν ⟩

      -- transformations monad
      pure : Γ ⊢ A -> Γ ⊢ Tr A
      seq : ∀{A : ⊢Type a} -> Γ ⊢ Tr A -> Γ ∙⟮ A ∣ id ⟯ ⊢ B -> Γ ⊢ Tr B

      -- functions
      lam : Γ ∙⟮ A ∣ id' ⟯ ⊢ B -> Γ ⊢ ⟮ A ∣ id' ⟯⇒ B
      app : Γ ⊢ ⟮ A ∣ μ ⟯⇒ B -> Γ ∙! μ ⊢ B -> Γ ⊢ B

    -- shift-＠ : ∀{i} -> {A : ⊢Type a} -> (Γ ∙! (`＠` i ⨾ id')) ∙⟮ A ∣ μ ⟯ ⊢ B -> (Γ ∙⟮ A ∣ μ ◆ (`＠` i ⨾ id') ⟯ ∙! (`＠` i ⨾ id')) ⊢ B
    -- shift-＠ = {!!}

    shift-＠ : ∀{i} -> {A : ⊢Type ▲} -> (Γ ∙! (`＠` i ⨾ id')) ∙⟮ A ∣ id' ⟯ ⊢ B -> (Γ ∙⟮ ⟨ A ∣ (`＠` i ⨾ id') ⟩ ∣ id' ⟯ ∙! (`＠` i ⨾ id')) ⊢ B
    shift-＠ = {!!}

    id-annotate : ∀{Γ : Ctx a} -> Γ ∙⟮ A ∣ μ ⟯ ⊢ B -> Γ ∙⟮ ⟨ A ∣ μ ⟩ ∣ id' ⟯ ⊢ B
    id-annotate = {!!}



  data isCtx₂ : Ctx a -> 𝒰₀ where
    ε : isCtx₂ {a = a} ε
    stepVar : {Γ : Ctx ◯} -> isCtx₂ Γ -> {A : ⊢Type a} -> {μ : a ⟶ ◯} -> isCtx₂ (Γ ∙⟮ A ∣ μ ⟯)
    stepRes-◻ : {Γ : Ctx ▲} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (`[]` ⨾ id))
    stepRes-＠ : {Γ : Ctx ◯} -> ∀{p} -> isCtx₂ Γ -> isCtx₂ (Γ ∙! (`＠` p ⨾ id))







  ⦋_⦌-Mode : Mode SRN-ModeSystem -> Mode'
  ⦋ ▲ ⦌-Mode = ▲
  ⦋ ◯ ⦌-Mode = ◯

  F-Type : (ModeHom' a b) -> Type ⦋ a ⦌-Mode -> Type ⦋ b ⦌-Mode
  F-Type id' x = x
  F-Type (`＠` U ⨾ μ) x = F-Type μ (x ＠ U)
  F-Type (`[]` ⨾ μ) x = F-Type μ (◻ x)

  ⦋_⦌-Type : ⊢Type a -> Type ⦋ a ⦌-Mode
  ⦋ ⟨ X ∣ μ ⟩ ⦌-Type = F-Type μ ⦋ X ⦌-Type
  ⦋ Unit ⦌-Type = Unit
  ⦋ Tr X ⦌-Type = Wrap ⦋ X ⦌-Type
  ⦋ ⟮ X ∣ μ ⟯⇒ Y ⦌-Type = F-Type μ ⦋ X ⦌-Type ⇒ ⦋ Y ⦌-Type


  TargetCtx : Mode SRN-ModeSystem -> 𝒰 _
  TargetCtx ▲ = Ctx' × ⟨ P ⟩
  TargetCtx ◯ = Ctx'


  transl-Ctx : ∀{μ : ModeHom' a ◯} -> (Γ : CtxExt μ) -> isCtx₂ (ε ⋆ Γ) -> TargetCtx a
  transl-Ctx ε Γp = ε
  transl-Ctx (Γ ∙⟮ x ∣ μ ⟯) (stepVar Γp) = transl-Ctx Γ Γp , F-Type μ ⦋ x ⦌-Type
  transl-Ctx (Γ ∙! (`[]` ⨾ id')) (stepRes-◻ Γp) = let Γ , i = transl-Ctx Γ Γp in Γ ,[ i ]
  transl-Ctx (Γ ∙! (`＠` i ⨾ id')) (stepRes-＠ Γp) = transl-Ctx Γ Γp , i

  -- ⦋ ε ⦌-Ctx = ε
  -- ⦋_⦌-Ctx {μ = μ} (Γ ∙⟮ x ∣ ν ⟯) = ⦋ Γ ⦌-Ctx , F-Type (ν ◆ μ) (⦋ x ⦌-Type)
  -- ⦋ Γ ∙! ω ⦌-Ctx = ⦋ Γ ⦌-Ctx


             -- -> ∑ λ δ -> ∀ p -> p ∈ ⟨ ps ⟩ -> ∀{Δ Δp} -> transl-Ctx Γ Γp ∣ p ↦ Δ , Δp Ctx -> Δ ⊢ ⦋ A ⦌-Type / δ GlobalFiber[ p ]

  mutual
    transl-Term-▲ : ∀{ps i} -> ∀{μ : ModeHom' ◯ ◯} -> (Γ : CtxExt μ) -> (Γp : isCtx₂ (ε ⋆ Γ))
              -> ∀{A} -> ε ⋆ Γ ∙! (`＠` i ⨾ id') ⊢ A
              -> ∑ λ δ -> transl-Ctx Γ Γp  ⊢ (⦋ A ⦌-Type ＠ i) / δ GlobalFibered[ ps ]
    transl-Term-▲ Γ Γp (var x α) = {!!}
    transl-Term-▲ Γ Γp tt = {!!}
    transl-Term-▲ Γ Γp (mod `[]` t) =
      let δ' , ts' = transl-Term-◯ _ (stepRes-◻ (stepRes-＠ Γp)) t
      in {!!} , {!!}
    transl-Term-▲ Γ Γp (letmod' `[]` t s) =
      let δt' , t' = transl-Term-▲ _ Γp t
          δs' , s' = transl-Term-▲ _ (stepVar Γp) (shift-＠ (id-annotate s))
      in {!? , app (lam t') ?!}
    transl-Term-▲ Γ Γp (letmod μ ν t s) = {!!}
      -- let δt' , t' = transl-Term-▲ Γ Γp t
      -- in ?
    transl-Term-▲ Γ Γp (trans x t) = {!!}
    transl-Term-▲ Γ Γp (pure t) = {!!}
    transl-Term-▲ Γ Γp (seq t t₁) = {!!}
    transl-Term-▲ Γ Γp (lam t) =
      let t' = shift-＠ t
          δ' , rest' = transl-Term-▲ _ (stepVar Γp) t'
      in {!lam◯ ?!} , commute-＠-Exp _ (lam-GlobalFibered rest')
    transl-Term-▲ Γ Γp (app t t₁) = {!!}


    transl-Term-◯ : ∀{ps} -> ∀{μ : ModeHom' ◯ ◯} -> (Γ : CtxExt μ) -> (Γp : isCtx₂ (ε ⋆ Γ))
              -> ∀{A} -> ε ⋆ Γ ⊢ A
              -> ∑ λ δ -> transl-Ctx Γ Γp  ⊢ ⦋ A ⦌-Type / δ GlobalFibered[ ps ]
    transl-Term-◯ Γ Γp (var x α) = {!!}
    transl-Term-◯ Γ Γp tt = {!!}
    transl-Term-◯ Γ Γp (mod (`＠` U) t) =
      let δ' , t' = transl-Term-▲ _ Γp t
      in δ' , t'
    transl-Term-◯ Γ Γp (letmod μ ν t t₁) = {!!}
    transl-Term-◯ Γ Γp (letmod' μ t t₁) = {!!}
    transl-Term-◯ Γ Γp (trans x t) = {!!}
    transl-Term-◯ Γ Γp (pure t) = {!!}
    transl-Term-◯ Γ Γp (seq t t₁) = {!!}
    transl-Term-◯ Γ Γp (lam t) =
      let δ' , t' = transl-Term-◯ _ (stepVar Γp) t
      in lam◯ δ' , lam-GlobalFibered t'
    transl-Term-◯ Γ Γp (app t t₁) = {!!}




{-
  ⦋_⦌-Term : ∀{ps} -> ∀{μ : ModeHom' a ◯} -> {Γ : CtxExt μ}
             -> ∀{A} -> ε ⋆ Γ ⊢ A
             -> ∑ λ δ -> ⦋ Γ ⦌-Ctx ⊢ ⦋ ⟨ A ∣ μ ⟩ ⦌-Type / δ GlobalFibered[ ps ]
  ⦋ var x α ⦌-Term = {!!}
  ⦋ tt ⦌-Term = {!!}
  ⦋ mod μ t ⦌-Term = {!!}
  ⦋ letmod ν t t₁ ⦌-Term = {!!}
  ⦋ trans x t ⦌-Term = {!!}
  ⦋ pure t ⦌-Term = {!!}
  ⦋ seq t t₁ ⦌-Term = {!!}
  ⦋_⦌-Term {μ = id} (lam t) =
    let δ' , t' = ⦋ t ⦌-Term
    in lam◯ δ' , lam-GlobalFibered t'
  ⦋_⦌-Term {μ = `＠` i ⨾ id} (lam {μ = id} t) =
    let δ' , t' = ⦋ t ⦌-Term
        t'' = lam-GlobalFibered t'
    in {!!} , commute-＠-Exp _ t''
  ⦋_⦌-Term {μ = μ} (lam t) = {!!}
    -- let δ' , t' = ⦋ t ⦌-Term
    -- in {!δ'!} , {!lam-GlobalFibered t'!}
  ⦋ app t s ⦌-Term = {!!}
    -- let δt' , t' = ⦋ t ⦌-Term
    --     δs' , s' = ⦋ s ⦌-Term
    -- in {!!}

-}










