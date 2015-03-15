module Relations.Minimum where

open import Function  using (id; _$_; _∘_)
open import Data.Product  using (Σ; _×_; _,_; proj₁; proj₂)
         renaming (map to map-×)

open import Sets
open import Relations
open import Relations.Factor
open import Relations.Converse

open import AlgebraicReasoning.Relations
open import AlgebraicReasoning.Implications

min : {A : Set} → (A ← A) → (A ← ℙ A)
min R = ∈ ⊓ (R / ∋)

max : {A : Set} → (A ← A) → (A ← ℙ A)
max R = min (R ˘)

-- min-universal : X ⊑ min R ₁∘ Λ S ⇔ (X ⊑ S  ×  X ○ (S ˘) ⊑ R)

min-universal-⇒ : {A B : Set} →
   {R : A ← A} {S : A ← B} {X : A ← B} →
     X ⊑ min R ₁∘ Λ S → (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
min-universal-⇒ {R = R} {S} {X} = 
   ⇒-begin 
     X ⊑ min R ₁∘ Λ S
   ⇒⟨  ⇒-refl  ⟩
     X ⊑ (∈ ⊓ (R / ∋)) ₁∘ Λ S
   ⇒⟨  ⊒-trans (⊓-Λ-distr-⊑ ∈ (R / ∋)) ⟩
     X ⊑ (∈ ₁∘ Λ S) ⊓ ((R / ∋) ₁∘ Λ S)
   ⇒⟨  ⊑-⊓ X (∈ ₁∘ Λ S) ((R / ∋) ₁∘ Λ S) ⟩
     (X ⊑ ∈ ₁∘ Λ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇒⟨  ⇒-refl  ⟩
     (X ⊑ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇒⟨  ⇒-refl  ⟩   -- /∋○Λ-cancelation-⊑ is deducible by Agda
     (X ⊑ S  ×  X ⊑ (R / S ˘))
   ⇒⟨  map-× id /-universal-⇐ ⟩
     (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
   ⇒∎

min-universal-⇐ : {A B : Set} →
   {R : A ← A} {S : A ← B} {X : A ← B} →
     (X ⊑ S  ×  X ○ (S ˘) ⊑ R) → X ⊑ min R ₁∘ Λ S
min-universal-⇐ {R = R} {S} {X} =
   ⇐-begin 
     X ⊑ min R ₁∘ Λ S
   ⇐⟨  ⇐-refl  ⟩
     X ⊑ (∈ ⊓ (R / ∋)) ₁∘ Λ S
   ⇐⟨ ⊒-trans (⊓-Λ-distr-⊒ ∈ (R / ∋)) ⟩
     X ⊑ (∈ ₁∘ Λ S) ⊓ ((R / ∋) ₁∘ Λ S)
   ⇐⟨ ⊓-universal-⇐ ⟩
     (X ⊑ ∈ ₁∘ Λ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇐⟨  ⇐-refl  ⟩
     (X ⊑ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇐⟨  ⇐-refl  ⟩   -- /∋○Λ-cancelation-⊒ is deducible by Agda
     (X ⊑ S  ×  X ⊑ (R / S ˘))
   ⇐⟨  map-× id /-universal-⇒ ⟩
     (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
   ⇐∎

min-universal : {A B : Set} →
   {R : A ← A} {S : A ← B} {X : A ← B} →
      X ⊑ min R ₁∘ Λ S  ⇔  (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
min-universal = (min-universal-⇒ , min-universal-⇐)

min-monotonic : {A B : Set} {R S : A ← A} {T : A ← B} →
  R ⊑ S → min R ₁∘ Λ T ⊑ min S ₁∘ Λ T
min-monotonic {_}{_} {R} {S} {T} =
  ⇐-begin
    min R ₁∘ Λ T ⊑ min S ₁∘ Λ T
  ⇐⟨ min-universal-⇐ ⟩
    (min R ₁∘ Λ T ⊑ T × (min R ₁∘ Λ T) ○ T ˘ ⊑ S)
  ⇐⟨ (λ next-line → (proj₁ $ min-universal-⇒ ⊑-refl) , next-line) ⟩
    (min R ₁∘ Λ T) ○ T ˘ ⊑ S
  ⇐⟨ ⊑-trans $ ○-monotonic-l $
        /-universal-⇒ $ proj₂ $ min-universal-⇒ ⊑-refl ⟩
    (R / (T ˘)) ○ T ˘ ⊑ S
  ⇐⟨ ⊑-trans $ /-universal-⇐ ⊑-refl ⟩
    R ⊑ S
  ⇐∎

max-monotonic : {A B : Set} {R S : A ← A} {T : A ← B} →
  R ⊑ S → max R ₁∘ Λ T ⊑ max S ₁∘ Λ T
max-monotonic = min-monotonic ∘ ˘-monotonic-⇐

corefl-propagation-⊑ : {A B : Set} {R : B ← B} {S : B ← A} {C : A ← A} →
  C ⊑ idR → (min R ₁∘ Λ S) ○ C ⊑ (min R ₁∘ Λ (S ○ C)) ○ C
corefl-propagation-⊑ {A} {B} {R} {S} {C} C⊑idR b a (a' , (bSa' , ∀b'-b'Sa'⇒bRb') , a'Ca)
  with C⊑idR a' a a'Ca
corefl-propagation-⊑ {A} {B} {R} {S} {C} C⊑idR b a (.a , (bSa , ∀b'-b'Sa⇒bRb') , aCa)
  | refl = a , (((a , bSa , aCa) , see-below) , aCa)
  where see-below : (b' : B) → Σ A (λ a' → S b' a' × C a' a) → R b b'
        see-below b' (a' , b'Sa' , a'Ca) with C⊑idR a' a a'Ca
        see-below b' (.a , b'Sa , aCa) | refl = ∀b'-b'Sa⇒bRb' b' b'Sa
corefl-propagation-⊒ : {A B : Set} {R : B ← B} {S : B ← A} {C : A ← A} →
  C ⊑ idR → (min R ₁∘ Λ S) ○ C ⊒ (min R ₁∘ Λ (S ○ C)) ○ C
corefl-propagation-⊒ C⊑idR b a (a' , ((a'' , bSa'' , a''Ca') , ∀b'-xCa'∧b'Sx⇒bRb') , a'Ca)
  with C⊑idR a' a a'Ca | C⊑idR a'' a' a''Ca'
corefl-propagation-⊒ C⊑idR b a (.a , ((.a , bSa , aCa₂) , ∀b'-xCa∧b'Sx⇒bRb') , aCa)
  | refl | refl = a , (bSa , λ b' b'Sa → ∀b'-xCa∧b'Sx⇒bRb' b' (a , b'Sa , aCa)) , aCa

minΛ-cong-⊒ : {A B : Set} {R : B ← B} {S T : B ← A} →
  (S ≑ T) → min R ₁∘ Λ S ⊒ min R ₁∘ Λ T
minΛ-cong-⊒ {R = R} {S} {T} (S⊑T , S⊒T) =
 (⇐-begin
    min R ₁∘ Λ T ⊑ min R ₁∘ Λ S
  ⇐⟨ min-universal-⇐ ⟩
    (min R ₁∘ Λ T ⊑ S × (min R ₁∘ Λ T) ○ S ˘ ⊑ R)
  ⇐⟨ map-× (⊑-trans $ proj₁ $ min-universal-⇒ ⊑-refl)
            (⊑-trans $ ○-monotonic-l $ /-universal-⇒ $ proj₂ $ min-universal-⇒ ⊑-refl) ⟩
    (T ⊑ S × (R / (T ˘)) ○ S ˘ ⊑ R)
  ⇐⟨ (λ next-line → S⊒T , next-line) ⟩
    (R / (T ˘)) ○ S ˘ ⊑ R
  ⇐⟨ ⊑-trans $ ○-monotonic-l $ /-anti-monotonic $ ˘-monotonic-⇐ S⊑T ⟩
    (R / (S ˘)) ○ S ˘ ⊑ R
  ⇐⟨ ⊑-trans $ /-universal-⇐ ⊑-refl ⟩
    R ⊑ R
  ⇐∎) ⊑-refl

thin : {A : Set} → (A ← A) → (ℙ A ← ℙ A)
thin Q = (∈ ﹨ ∈) ⊓ ((∋ ○ Q) / ∋)

-- thin-universal-⇐ :
--    ₁⊑ thin Q ₁∘ Λ S ⇔ (X ₁⊑ ∈ ₁﹨ S  ₁×₁  X ₁○ (S ˘) ₁⊑ ∋ ₁○ Q)

thin-universal-⇐ : {A B : Set} →
   {Q : A ← A} {S : A ← B} → (X : ℙ A ← B) →
     X ⊑ thin Q ₁∘₁ Λ S → (X ⊑ ∈ ﹨ S  ×  X ○ (S ˘) ⊑ ∋ ○ Q)
thin-universal-⇐ {Q = Q}{S} X = 
   ⇒-begin
     X ⊑ thin Q ₁∘₁ Λ S
   ⇒⟨  ⇒-refl  ⟩
     X ⊑ ((∈ ﹨ ∈) ⊓ ((∋ ○ Q) / ∋)) ₁∘₁ Λ S
   ⇒⟨  ⊒-trans (₁⊓₁-Λ-distr (∈ ﹨ ∈) ((∋ ○ Q) / ∋))   ⟩
     X ⊑ ((∈ ﹨ ∈) ₁∘₁ Λ S) ⊓ (((∋ ○ Q) / ∋) ₁∘₁ Λ S)
   ⇒⟨  ⊑-⊓ X ((∈ ﹨ ∈) ₁∘₁ Λ S) (((∋ ○ Q) / ∋) ₁∘₁ Λ S)   ⟩
     (X ⊑ (∈ ﹨ ∈) ₁∘₁ Λ S  ×  X ⊑ ((∋ ○ Q) / ∋) ₁∘₁ Λ S)
   ⇒⟨  ⇒-refl  ⟩
     (X ⊑ ∈ ﹨ S  ×  X ⊑ ((∋ ○ Q) / ∋) ₁∘₁ Λ S)
   ⇒⟨  ⇒-refl   ⟩
     (X ⊑ ∈ ﹨ S  ×  X ⊑ (∋ ○ Q) / (S ˘))
   ⇒⟨  map-× (λ x → x) /-universal-⇐  ⟩
     (X ⊑ ∈ ﹨ S  ×  X ○ (S ˘) ⊑ ∋ ○ Q)
   ⇒∎

