{-# OPTIONS --overlapping-instances #-}

module Sort where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Data.List using (List; _∷_; [])

open import Data.Variant using (Variants; inj; `_)


-- instance search methods

open import Data.List.Membership.Propositional.Instances 
  using (⦃here⦄; ⦃there⦄)
open import Data.List.Relation.Binary.Subset.Propositional.Instances
  using (⦃[]⊆xs⦄; ⦃x∈ys-xs⊆ys⇒x∷xs⊆ys⦄; ⦅_⊆_⦆)
open import Data.Union.Relation.Binary.Subtype.Instances 
  using (⦃refl⦄; ⦃generalize⦄; ⦃function⦄; ⌊_⌋)


-- ----------------------------------------------------------------------
-- Example (Injections)

data Sort : Set where
  term type : Sort 

_ : Variants Sort (term ∷ [])
_ = ` term

_-Bounds : List Sort → Set
𝒮 -Bounds = Variants Sort 𝒮 → ℕ  

Index : {𝒮 : List Sort} → Variants Sort 𝒮 → (𝒮 -Bounds) → Set
Index 𝓈 Γ = Fin (Γ 𝓈)

term-sorts : List Sort
term-sorts = term ∷ type ∷ []

infix 9 #_
data Term : term-sorts -Bounds → Set where
  #_ : ∀ {Γ} → Index (` term) Γ → Term Γ

-- ----------------------------------------------------------------------
-- Example (Subtyping)

type-sorts : List Sort
type-sorts = type ∷ []

infix 9 ~_

data Type : type-sorts -Bounds → Set where
  ~_ : ∀ {Γ} → Index (` type) Γ → Type Γ

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

_ : ⦅ type-sorts ⊆ term-sorts ⦆
_ = it

_ : term-sorts -Bounds → Set
_ = ⌊ Type ⌋

infixl 7 _[_]

data Term′ : term-sorts -Bounds → Set where
  #_ : ∀ {Γ} → Index (` term) Γ → Term′ Γ
  _[_] : ∀ {Γ} → Term′ Γ → ⌊ Type ⌋ Γ → Term′ Γ 