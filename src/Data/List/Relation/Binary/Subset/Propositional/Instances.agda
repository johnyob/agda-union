module Data.List.Relation.Binary.Subset.Propositional.Instances where

open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary.Negation using (contradiction)

open import Relation.Binary.PropositionalEquality using (sym; setoid)

open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    x y : A
    xs ys : List A


-- ----------------------------------------------------------------------
-- Wrapped subset. Could use Data.Wrap but required curried arguments
-- Easier to define specific data type. 

infix 4 ⦅_⊆_⦆
data ⦅_⊆_⦆ {a} {A : Set a} : List A → List A → Set a where
  [_] : xs ⊆ ys → ⦅ xs ⊆ ys ⦆

proj : ⦅ xs ⊆ ys ⦆ → xs ⊆ ys
proj [ xs⊆ys ] = xs⊆ys

-- ----------------------------------------------------------------------
-- Lemmas used for instance searching

x∉[] : x ∉ []
x∉[] = λ ()

[]⊆xs : [] ⊆ xs
[]⊆xs = λ x∈[] → contradiction x∈[] x∉[]

xs⊆x∷xs : xs ⊆ x ∷ xs
xs⊆x∷xs = there

xs⊆ys⇒x∷xs⊆x∷ys : xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
xs⊆ys⇒x∷xs⊆x∷ys xs⊆ys (here y≡x) = here y≡x
xs⊆ys⇒x∷xs⊆x∷ys xs⊆ys (there y∈x∷xs) = there (xs⊆ys y∈x∷xs)

x∈ys-xs⊆ys⇒x∷xs⊆ys : x ∈ ys → xs ⊆ ys → x ∷ xs ⊆ ys
x∈ys-xs⊆ys⇒x∷xs⊆ys x∈ys xs⊆ys (here y≡x) = ∈-resp-≈ (setoid _) (sym y≡x) x∈ys
x∈ys-xs⊆ys⇒x∷xs⊆ys x∈ys xs⊆ys (there y∈x∷xs) = xs⊆ys y∈x∷xs

-- ----------------------------------------------------------------------
-- Instances

instance
  ⦃[]⊆xs⦄ : ⦅ [] ⊆ xs ⦆
  ⦃[]⊆xs⦄ = [ []⊆xs ]

  -- Removed to improve instance search, syntax directed. 
  
  -- ⦃xs⊆x∷xs⦄ : ⦅ xs ⊆ x ∷ xs ⦆
  -- ⦃xs⊆x∷xs⦄ = [ xs⊆x∷xs ]

  -- ⦃xs⊆ys⇒x∷xs⊆x∷ys⦄ : ⦃ ⦅ xs ⊆ ys ⦆ ⦄ → ⦅ x ∷ xs ⊆ x ∷ ys ⦆
  -- ⦃xs⊆ys⇒x∷xs⊆x∷ys⦄ ⦃ [ xs⊆ys ] ⦄ = [ xs⊆ys⇒x∷xs⊆x∷ys xs⊆ys ]

  ⦃x∈ys-xs⊆ys⇒x∷xs⊆ys⦄ : ⦃ x ∈ ys ⦄ → ⦃ ⦅ xs ⊆ ys ⦆ ⦄ → ⦅ x ∷ xs ⊆ ys ⦆
  ⦃x∈ys-xs⊆ys⇒x∷xs⊆ys⦄ ⦃ x∈ys ⦄ ⦃ [ xs⊆ys ] ⦄ = [ x∈ys-xs⊆ys⇒x∷xs⊆ys x∈ys xs⊆ys ]
