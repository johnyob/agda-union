module Data.Union where

open import Data.List using (List; _∷_; [_]; [])
open import Data.List.Relation.Unary.Any using (here; there; _─_)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Maybe using (Maybe; just; nothing; _>>=_)

open import Level using (Level; _⊔_)

open import Function using (_∘_)

-- ----------------------------------------------------------------------
-- Definition
-- 
-- A union of the family B defined by the list of tags ts 
-- of type A

data Union {a b} (A : Set a) (B : A → Set b) : List A → Set (a ⊔ b) where
  here : ∀ {t ts} → B t → Union A B (t ∷ ts) 
  there : ∀ {t ts} → Union A B ts → Union A B (t ∷ ts)

-- ----------------------------------------------------------------------
-- Injection and projections to (and from) unions

private
  variable
    a b : Level
    A : Set a
    B : A → Set b
    t : A
    ts ts′ : List A

inj : t ∈ ts → B t → Union A B ts
inj (here t≡t′) x rewrite t≡t′ = here x
inj (there t∈ts) x = there (inj t∈ts x)

`_ : ⦃ t ∈ ts ⦄ → B t → Union A B ts
`_ ⦃ t∈ts ⦄ x = inj t∈ts x

proj : t ∈ ts → Union A B ts → Maybe (B t)
proj (here t≡t′) (here x) rewrite t≡t′ = just x
proj (there t∈ts) (here x) = nothing
proj (here t≡t′) (there x) = nothing
proj (there t∈ts) (there x) = proj t∈ts x

`proj : ⦃ t ∈ ts ⦄ → Union A B ts → Maybe (B t)
`proj ⦃ t∈ts ⦄ x = proj t∈ts x

proj₀ : Union A B [ t ] → B t
proj₀ (here x) = x

remove : Union A B ts → (i : t ∈ ts) → Maybe (Union A B (ts ─ i))
remove (here x) (here _) = nothing
remove (here x) (there _) = just (here x)
remove (there x) (here _) = just x
remove (there x) (there t∈ts) = remove x t∈ts >>= just ∘ there



