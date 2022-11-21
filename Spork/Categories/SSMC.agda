module Spork.Categories.SSMC where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal

module _ {ℓC ℓC' ℓD ℓD' : Level}
         (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') where
  open Functor

  ×C-comm : Functor (C × D) (D × C)
  ×C-comm .F-ob (x , y) = y , x
  ×C-comm .F-hom (f , g) = g , f
  ×C-comm .F-id = refl
  ×C-comm .F-seq _ _ = refl

record SSMC ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    M : StrictMonCategory ℓ ℓ'

  open StrictMonCategory M public

  private
    [x⊗y] : Functor (C × C) C
    [x⊗y] = ─⊗─

    [y⊗x] : Functor (C × C) C
    [y⊗x] = ─⊗─ ∘F ×C-comm C C

  field
    B : [x⊗y] ≅ᶜ [y⊗x]

  open NatTrans
  open NatIso

  B⟨_,_⟩ : (x y : ob) → Hom[ x ⊗ y , y ⊗ x ]
  B⟨ x , y ⟩ = B .trans ⟦ (x , y) ⟧

  field
    B⋆B≡id : ∀ x y → B⟨ y , x ⟩ ⋆ B⟨ x , y ⟩ ≡ id

  private
    α⟨_,_,_⟩ : (x y z : ob) → Hom[ (x ⊗ y) ⊗ z , x ⊗ (y ⊗ z) ]
    α⟨ x , y , z ⟩ = idP {C = C} {p = sym (assoc x y z)}

  field
    hexagon : ∀ x y z →
      α⟨ x , y , z ⟩ ⋆ B⟨ x , y ⊗ z ⟩ ⋆ α⟨ y , z , x ⟩
        ≡ B⟨ x , y ⟩ ⊗ₕ id ⋆ α⟨ y , x , z ⟩ ⋆ id ⊗ₕ B⟨ x , z ⟩
