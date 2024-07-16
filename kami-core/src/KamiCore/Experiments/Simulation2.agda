
{-# OPTIONS --allow-unsolved-metas --rewriting --guardedness #-}

module KamiCore.Typed.Variant.F.Simulation2 where

open import Agora.Conventions hiding (k ; m ; n ; _∣_ ; _⊔_ ; ls)
open import Agora.Data.Product.Definition
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Data.Nat.Properties using (+-comm)



-- We have maps a ≤ (a ∨ b). Thus if a ∨ b is equal to zero, then
-- it should be 0 ≤ a ≤ 1. Then we have a ∨ 1 = 1. And a ∨ 0 = a.



-- We need an infinite sequence of types which all depend on each other.

record 𝕍 𝑖 : 𝒰 (𝑖 ⁺) where
  coinductive
  field P : JoinSemilattice 𝑖
  field N : JoinSemilattice 𝑖
  field T : ⟨ N ⟩ -> 𝕍 𝑖

open 𝕍 public

record Impl (v : 𝕍 𝑖) : 𝒰 𝑖 where
  coinductive
  field p : ⟨ P v ⟩
  field n : (n : ⟨ N v ⟩) -> Impl (T v n)


record Open (v : 𝕍 𝑖) : 𝒰 (𝑖 ⁺) where
  coinductive
  field p : ⟨ P v ⟩
  field Ix : 𝒰 𝑖
  field n : Ix -> ⟨ N v ⟩
  field t : ∀ i -> Open (T v (n i))

-- record _⊑_ {v : 𝕍 𝑖} (U V : Open v) : 𝒰 (𝑖 ⁺) where
--   coinductive
--   field p : p U ≤ p V



