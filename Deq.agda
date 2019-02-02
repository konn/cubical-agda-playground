{-# OPTIONS --cubical #-}
module Deq where
import Level renaming (suc to sucL)
open import Cubical.Core.Everything
open import Cubical.Core.Id using (pathId)
import Cubical.Core.Id as Id
open import Cubical.Core.HoTT-UF using (transport)
open import Missing.List using (List)
import Missing.List as L
import Missing.List.Properties as L
open import Missing.Function
open import Missing.FunctionProperties
open import Missing.EqReasoning

data Deq {𝓁} (A : Set 𝓁) : Set 𝓁 where
  mkQ    : List A → List A → Deq A
  rotate : (a : A) (l r : List A) → mkQ (l L.∷ʳ a) r ≡ mkQ l (r L.∷ʳ a)

pattern [] = mkQ L.[] L.[]

module _ {𝓁} {A : Set 𝓁} where
  infixr 5 _∷_
  _∷_ : A → Deq A → Deq A
  x ∷ mkQ l r = mkQ (x L.∷ l) r
  x ∷ rotate a l r i = rotate a (x L.∷ l) r i

  infixl 5 _∷ʳ_
  _∷ʳ_ : Deq A → A → Deq A
  mkQ l r        ∷ʳ x = mkQ l (x L.∷ r)
  rotate a l r i ∷ʳ x = rotate a l (x L.∷ r) i

  reverse : Deq A → Deq A
  reverse (mkQ l r) = mkQ r l
  reverse (rotate a l r i) = rotate a r l (~ i)

  map : ∀ {𝓁′} {B : Set 𝓁′} → (A → B) → Deq A → Deq B
  map f (mkQ l r) = mkQ (L.map f l) (L.map f r)
  map  {_} {B} f (rotate a l r i) = 
    let pf =  mkQ (L.map f (l L.∷ʳ a)) (L.map f r)
            ≡⟨ cong
                (λ xs → mkQ xs $ L.map f r) $
                L.map-++-commute f l L.[ a ]
             ⟩ 
              mkQ (L.map f l L.∷ʳ f a) (L.map f r)
            ≡⟨ rotate (f a) (L.map f l) (L.map f r) ⟩
              mkQ (L.map f l) (L.map f r  L.∷ʳ f a)
            ≡⟨ cong
                (λ ys → mkQ (L.map f l) ys) $
                sym $ L.map-++-commute f r L.[ a ]
              ⟩
              mkQ (L.map f l) (L.map f (r L.∷ʳ a))
            ∎
    in pf i

  module _ where
    aux-app-rev : ∀ (a : A) (l r : List A)
                → l L.++ L.reverse (r L.∷ʳ a) ≡ (l L.∷ʳ a) L.++ L.reverse r
    aux-app-rev a l r = 
        l L.++ L.reverse (r L.∷ʳ a)
      ≡⟨ cong (l L.++_) $ L.reverse-++-commute r _ ⟩
        l L.++ (L.[ a ] L.++ L.reverse r)
      ≡⟨ sym $ L.++-assoc l _ _ ⟩
        (l L.∷ʳ a) L.++ L.reverse r
      ∎

    aux-que-app-rev : ∀ (l m r : List A) → mkQ (l L.++ m) r ≡ mkQ l (r L.++ L.reverse m)
    aux-que-app-rev l L.[] r =
        mkQ (l L.++ L.[]) r
      ≡⟨ cong (λ x → mkQ x r) $ L.++-identityʳ l ⟩
        mkQ l r
      ≡⟨ cong (mkQ l) (sym $ L.++-identityʳ r) ⟩
        mkQ l (r L.++ L.[])
      ≡⟨⟩
        mkQ l (r L.++ L.reverse L.[])
      ∎
    aux-que-app-rev l (x L.∷ xs) r =
        mkQ (l L.++ (x L.∷ xs)) r
      ≡⟨⟩
        mkQ (l L.++ (L.[ x ] L.++ xs)) r
      ≡⟨ cong (λ l → mkQ l r) $ sym $ 
          L.++-assoc l L.[ x ] xs
       ⟩
        mkQ ((l L.∷ʳ x) L.++ xs) r
      ≡⟨ aux-que-app-rev (l L.∷ʳ x) xs r ⟩
        mkQ (l L.∷ʳ x) (r L.++ L.reverse xs)
      ≡⟨ rotate x l (r L.++ L.reverse xs) ⟩
        mkQ l ((r L.++ L.reverse xs) L.∷ʳ x)
      ≡⟨ cong (mkQ l) $ 
          L.++-assoc r (L.reverse xs) L.[ x ]
       ⟩
        mkQ l (r L.++ (L.reverse xs L.∷ʳ x))
      ≡⟨ cong (λ zs → mkQ l (r L.++ zs)) $ sym $ 
          L.unfold-reverse x xs
       ⟩
        mkQ l (r L.++ L.reverse (x L.∷ xs))
      ∎

  to-list : Deq A → List A
  to-list (mkQ l r) = l L.++ L.reverse r
  to-list (rotate a l r i) =
      ( (l L.∷ʳ a) L.++ L.reverse r
      ≡⟨ L.++-assoc l _ _ ⟩
        l L.++ (L.[ a ] L.++ L.reverse r)
      ≡⟨ sym $ cong (l L.++_) $ L.reverse-++-commute r _ ⟩
        l L.++ L.reverse (r L.∷ʳ a)
      ∎
     ) i

  to-revlist : Deq A → List A
  to-revlist (mkQ l r) = r L.++ L.reverse l
  to-revlist (rotate a l r i) =
     aux-app-rev a r l i

  infixr 5 _++_
  _++_ : Deq A → Deq A → Deq A
  l ++ r = mkQ (to-list l) (to-revlist r)

  module Properties where
    ++-identityʳ-base : ∀(l r : List A) → mkQ l r ++ [] ≡ mkQ l r
    ++-identityʳ-base l r =
        (mkQ (l L.++ L.reverse r) L.[])
      ≡⟨ aux-que-app-rev l (L.reverse r) L.[] ⟩
        (mkQ l (L.reverse (L.reverse r)))
      ≡⟨ cong (mkQ l) (L.reverse-involutive r) ⟩
        mkQ l r
      ∎

    ++-identityʳ-i : ∀(a : A) (l r : List A) (j₀ : I) → rotate a l r j₀ ++ [] ≡ rotate a l r j₀
    ++-identityʳ-i a l r j₀ i =
      hfill
        (λ j → λ { (i = i0) → rotate a l r j ++ [] 
                 ; (i = i1) → rotate a l r j
                 })
        (inc (++-identityʳ-base (l L.∷ʳ a) r i))
        j₀

    ++-identityʳ : RightIdentity [] _++_
    ++-identityʳ (mkQ l r) = ++-identityʳ-base l r
    ++-identityʳ (rotate a l r j₀) i = {! ++-identityʳ-i a l r j₀ i !} -- ^ Why doesn't this work?

      
    {-
    ++-identityˡ : LeftIdentity {A = Deq A} _≡_ [] _++_
    ++-identityˡ (mkQ l r) =
        [] ++ mkQ l r
      ≡⟨⟩
        mkQ L.[] (r L.++ L.reverse l)
      ≡⟨ sym $ aux-que-app-rev L.[] l r ⟩
        mkQ l r
      ∎

    ++-assoc : Associative {A = Deq A} _≡_ _++_
    ++-assoc (mkQ l₁ r₁) (mkQ l₂ r₂) (mkQ l₃ r₃) = 
        (mkQ l₁ r₁ ++ mkQ l₂ r₂) ++ mkQ l₃ r₃
      ≡⟨⟩
        mkQ (l₁ L.++ L.reverse r₁) (r₂ L.++ L.reverse l₂) ++ mkQ l₃ r₃
      ≡⟨⟩
        mkQ ((l₁ L.++ L.reverse r₁) L.++ L.reverse (r₂ L.++ L.reverse l₂)) (r₃ L.++ L.reverse l₃)
      ≡⟨ cong (λ targ → mkQ ((l₁ L.++ L.reverse r₁) L.++ targ) (r₃ L.++ L.reverse l₃)) $
            L.reverse (r₂ L.++ L.reverse l₂)
          ≡⟨ L.reverse-++-commute r₂ _ ⟩
            L.reverse (L.reverse l₂) L.++ L.reverse r₂
          ≡⟨ cong (L._++ L.reverse r₂) $
              L.reverse-involutive l₂
           ⟩
            l₂ L.++ L.reverse r₂
          ∎
       ⟩
        mkQ ((l₁ L.++ L.reverse r₁) L.++ (l₂ L.++ L.reverse r₂)) (r₃ L.++ L.reverse l₃)
      ≡⟨ aux-que-app-rev (l₁ L.++ L.reverse r₁) _ (r₃ L.++ L.reverse l₃) ⟩
        mkQ (l₁ L.++ L.reverse r₁) ((r₃ L.++ L.reverse l₃) L.++ L.reverse (l₂ L.++ L.reverse r₂))
      ≡⟨⟩
        mkQ l₁ r₁ ++ mkQ (l₂ L.++ L.reverse r₂) (r₃ L.++ L.reverse l₃)
      ≡⟨⟩
        mkQ l₁ r₁ ++ (mkQ l₂ r₂ ++ mkQ l₃ r₃)
      ∎ -}
    
     
