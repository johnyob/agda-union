module Data.List.Membership.Propositional.Instances where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Binary.PropositionalEquality using (refl)

open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    x y : A
    xs : List A

instance 
  ⦃here⦄ : x ∈ x ∷ xs
  ⦃here⦄ = here refl

  ⦃there⦄ : ⦃ x ∈ xs ⦄ → x ∈ y ∷ xs
  ⦃there⦄ ⦃ x∈xs ⦄ = there x∈xs
