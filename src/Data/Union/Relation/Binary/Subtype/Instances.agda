module Data.Union.Relation.Binary.Subtype.Instances where

open import Data.List using (List)
open import Data.List.Relation.Binary.Subset.Propositional.Instances using (⦅_⊆_⦆; [_])

open import Data.Union using (Union)
open import Data.Union.Relation.Binary.Subtype 
  using (_≼_; _,_⊢_≼_; refl; trans; generalize; function)

open import Level using (Level; _⊔_)

private
  variable
    a b c d f : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

    F : A → Set f
    ts ts′ : List A

-- ----------------------------------------------------------------------
-- Wrapped subtypes

infix 4 ⦅_≼_⦆ ⦅_,_⊢_≼_⦆

data ⦅_≼_⦆ {a b} : Set a → Set b → Set (a ⊔ b) where
  [_] : A ≼ B → ⦅ A ≼ B ⦆

⦅_,_⊢_≼_⦆ : (A : Set a) → (B : A → Set b) → List A → List A → Set (a ⊔ b)
⦅ A , B ⊢ ts ≼ ts′ ⦆ = ⦅ Union A B ts ≼ Union A B ts′ ⦆

proj : ⦅ A ≼ B ⦆ → A ≼ B
proj [ A≼B ] = A≼B

⊢proj : ⦅ A , F ⊢ ts ≼ ts′ ⦆ → A , F ⊢ ts ≼ ts′
⊢proj [ A,F⊢ts≼ts′ ] = A,F⊢ts≼ts′

-- ----------------------------------------------------------------------
-- Instances

instance
  ⦃refl⦄ : ⦅ A ≼ A ⦆
  ⦃refl⦄ = [ refl ]

  -- Removed since the transitivity of ⊆ provides this
  -- Also now allows for syntax directed instance search :) 
  
  -- ⦃trans⦄ : ⦃ ⦅ A ≼ B ⦆ ⦄ → ⦃ ⦅ B ≼ C ⦆ ⦄ → ⦅ A ≼ C ⦆
  -- ⦃trans⦄ ⦃ [ A≼B ] ⦄ ⦃ [ B≼C ] ⦄ = [ trans A≼B B≼C ]

  ⦃generalize⦄ : ⦃ ⦅ ts ⊆ ts′ ⦆ ⦄ → ⦅ A , F ⊢ ts ≼ ts′ ⦆
  ⦃generalize⦄ ⦃ [ ts⊆ts′ ] ⦄ = [ generalize ts⊆ts′ ]

  ⦃function⦄ : ⦃ ⦅ C ≼ A ⦆ ⦄ → ⦃ ⦅ B ≼ D ⦆ ⦄ → ⦅ (A → B) ≼ (C → D) ⦆
  ⦃function⦄ ⦃ [ C≼A ] ⦄ ⦃ [ B≼D ] ⦄ = [ function C≼A B≼D ]

-- ----------------------------------------------------------------------
-- Coercion using instance search

⌊_⌋ : ⦃ ⦅ A ≼ B ⦆ ⦄ → A → B
⌊_⌋ ⦃ [ A≼B ] ⦄ A = A≼B A