module Data.Union.Relation.Binary.Subtype where

open import Data.List using (List)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Data.Union using (Union; here; there; inj)

open import Function using (_∘_; id)

open import Relation.Binary.PropositionalEquality using () renaming (refl to refl≡)

open import Level using (Level; _⊔_)

-- ----------------------------------------------------------------------
-- Subtyping

private
  variable
    a b c d f : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

    F : A → Set f
    ts ts′ : List A


infix 4 _≼_ _,_⊢_≼_

_≼_ : Set a → Set b → Set (a ⊔ b)
A ≼ B = A → B

_,_⊢_≼_ : (A : Set a) → (F : A → Set b) → List A → List A → Set (a ⊔ b)
A , F ⊢ ts ≼ ts′ = Union A F ts ≼ Union A F ts′

refl : A ≼ A
refl = id

trans : A ≼ B → B ≼ C → A ≼ C
trans A≼B B≼C = B≼C ∘ A≼B

generalize : ts ⊆ ts′ → A , F ⊢ ts ≼ ts′
generalize ts⊆ts′ (here x) = inj (ts⊆ts′ (here refl≡)) x
generalize ts⊆ts′ (there x) = generalize (ts⊆ts′ ∘ there) x

function : C ≼ A → B ≼ D → (A → B) ≼ (C → D) 
function C≼A B≼D f = B≼D ∘ f ∘ C≼A

coerce : A ≼ B → A → B
coerce = id