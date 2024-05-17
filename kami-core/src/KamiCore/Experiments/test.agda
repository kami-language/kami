
module KamiCore.Experiments.test where


module Version1 where
  mutual
    data Ctx : Set where
      _,_ : (Γ : Ctx) -> Type Γ -> Ctx

    data Type : Ctx -> Set where
      Pi : ∀{Γ A} -> Type (Γ , A) -> Type Γ



module Version2 where

  data Ctx : Set
  data Type : Ctx -> Set

  data Ctx where
    _,_ : (Γ : Ctx) -> Type Γ -> Ctx

  data Type where
    Pi : ∀{Γ A} -> Type (Γ , A) -> Type Γ



data Boolean : Set where
  true : Boolean
  false : Boolean


reverse : Boolean -> Boolean
reverse true = false
reverse false = true

example : Boolean
example = reverse(reverse(false))


theorem : ∀ x -> reverse (reverse (x)) ≡ x
theorem true = refl-≡
theorem false = refl-≡


