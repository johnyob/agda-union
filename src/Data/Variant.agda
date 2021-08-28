module Data.Variant where

open import Data.List using (List) renaming ([_] to [_]ₗ)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Product using (∃; ∃-syntax; _,_)

open import Data.Maybe using (Maybe; _>>=_; just)

open import Data.Union using (Union; here) renaming (inj to injᵤ; proj to projᵤ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Level using (Level)

-- ----------------------------------------------------------------------
-- Definitions

-- A variant is tagged tag. It is motiviated by the existence
-- of familys of tags. 

data Variant {a} (A : Set a) : A → Set a where
  -- injects a into a Variant indexed by a
  [_] : (a : A) → Variant A a

-- A polymorphic variant is a open union of variants

Variants : ∀ {a} (A : Set a) → List A → Set a
Variants A ts = Union A (Variant A) ts

-- ----------------------------------------------------------------------
-- Injections and projects to (and from) variants

private
  variable
    a b : Level
    A : Set a
    t : A
    ts ts′ : List A

inj : (t : A) → t ∈ ts → Variants A ts
inj t t∈ts = injᵤ t∈ts ([ t ])

`_ : (t : A) → ⦃ t ∈ ts ⦄ → Variants A ts
`_ t ⦃ t∈ts ⦄ = inj t t∈ts

Proj : ∀ {a} (A : Set a) → (t : A) → Set a
Proj A t = ∃ λ t′ → t ≡ t′

proj : t ∈ ts → Variants A ts → Maybe (Proj A t)
proj t∈ts x = projᵤ t∈ts x >>= λ{ [ t ] → just (t , refl)}

`proj : ⦃ t ∈ ts ⦄ → Variants A ts → Maybe (Proj A t)
`proj ⦃ t∈ts ⦄ x = proj t∈ts x

proj₀ : Variants A [ t ]ₗ → Proj A t
proj₀ (here [ t ]) = t , refl

