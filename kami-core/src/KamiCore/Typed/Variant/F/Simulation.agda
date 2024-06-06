
{-# OPTIONS --allow-unsolved-metas --rewriting --guardedness #-}

module KamiCore.Typed.Variant.F.Simulation where

open import Agora.Conventions hiding (k ; m ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Data.Nat.Properties using (+-comm)



-- We need an infinite sequence of types which all depend on each other.

record 𝕍 𝑖 : 𝒰 (𝑖 ⁺) where
  coinductive
  field H : 𝒰 𝑖
  field T : H -> 𝕍 𝑖

open 𝕍 public



mutual
  data BaseOpen {𝑖} : 𝕍 𝑖 -> 𝒰 (𝑖 ⁺) where
    [] : ∀{v} -> BaseOpen v
    _∷_ : ∀{v} -> (h : H v) -> Point (T v h) -> BaseOpen v

  data Point {𝑖} : 𝕍 𝑖 -> 𝒰 (𝑖 ⁺) where
    _∷_ : ∀{v} -> (h : H v) -> BaseOpen (T v h) -> Point v

record Trace (v : 𝕍 𝑖) : 𝒰 𝑖 where
  coinductive
  field h : H v
  field t : Trace (T v h)

mutual
  record Impl-∀ (v : 𝕍 𝑖) : 𝒰 𝑖 where
    constructor Ev
    coinductive
    field eval : ∀(h : H v) -> Impl-∃ (T v h)

  record Impl-∃ (v : 𝕍 𝑖) : 𝒰 𝑖 where
    constructor _,_
    coinductive
    field fst : H v
    field snd : Impl-∀ (T v fst)



empty : 𝕍 𝑖
𝕍.H empty = 𝟙
𝕍.T empty = λ x → empty

mutual
  vempty-∀ : Impl-∀ {𝑖} empty
  Impl-∀.eval vempty-∀ h = vempty-∃

  vempty-∃ : Impl-∃ {𝑖} empty
  Impl-∃.fst vempty-∃ = tt
  Impl-∃.snd vempty-∃ = vempty-∀

module Example where
  v0 : 𝕍 ℓ₀
  𝕍.H v0 = ℕ
  𝕍.H (𝕍.T v0 x) = 𝟙
  𝕍.H (𝕍.T (𝕍.T v0 x) x₁) = ℕ
  𝕍.H (𝕍.T (𝕍.T (𝕍.T v0 x) x₁) x₂) = x +-ℕ x₂ ≡ x₂ +-ℕ x
  𝕍.H (𝕍.T (𝕍.T (𝕍.T (𝕍.T v0 x) x₁) x₂) x₃) = 𝟙
  𝕍.T (𝕍.T (𝕍.T (𝕍.T (𝕍.T v0 x) x₁) x₂) x₃) x4 = empty

  i0 : Impl-∀ v0
  i0 = Ev λ a → tt , Ev λ b → +-comm a b , Ev λ h → tt , vempty-∀

  p0 : Point v0
  p0 = 1 ∷ []

  p1 : Point v0
  p1 = 1 ∷ tt ∷ 2 ∷ []

  p2 : Point v0
  p2 = 1 ∷ tt ∷ 2 ∷ refl-≡ ∷ tt ∷ []





