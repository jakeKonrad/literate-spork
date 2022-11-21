module Spork.Categories.Traced where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal
open import Spork.Categories.SSMC

record TracedMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    M : SSMC ℓ ℓ'

  open SSMC M public

  field
    Tr : (x a b : ob) → Hom[ a ⊗ x , b ⊗ x ] → Hom[ a , b ]
    vanishing₁ : ∀ a b f → (λ i → Hom[ idr a (~ i) , idr b (~ i) ]) [ Tr unit a b f ≡ f ]
    vanishing₂ : ∀ x y a b f →
      Tr (x ⊗ y) a b f
        ≡ Tr x a b (Tr y (a ⊗ x) (b ⊗ x)
            (transport (λ i → Hom[ assoc a x y i , assoc b x y i ]) f))
    superposing : ∀ x a b c f →
      Tr x (c ⊗ a) (c ⊗ b)
        (transport (λ i → Hom[ assoc c a x i , assoc c b x i ]) (id ⊗ₕ f))
          ≡ id ⊗ₕ Tr x a b f
    yanking : ∀ x → Tr x x x B⟨ x , x ⟩ ≡ id
