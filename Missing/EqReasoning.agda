{-# OPTIONS --safe --cubical #-}
module Missing.EqReasoning where
open import Cubical.Core.Everything public
  using (_≡⟨_⟩_ ; _∎ ; _≡_)

infixr 2 _≡⟨⟩_
_≡⟨⟩_ : ∀{𝓁} {A : Set 𝓁} (x : A) {y : A} → x ≡ y → x ≡ y
_ ≡⟨⟩ e = e
