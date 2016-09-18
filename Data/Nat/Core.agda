-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Nat.Core where

open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
  using (suc; zero; _+_; _*_)
open import Core


instance
  ℕ-Number : Number ℕ
  ℕ-Number =
    record {
      Constraint = λ _ → ⊤;
      fromNat = λ n → n
    }


≡ : Equiv ℕ
≡ = PropEq ℕ


module Props where
  open Equiv (PropEq ℕ)

  +-assoc : ∀ x y z → (x + y) + z ≈ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)

  +-left-id : ∀ x → 0 + x ≈ x
  +-left-id _ = refl

  +-right-id : ∀ x → x + 0 ≈ x
  +-right-id zero = refl
  +-right-id (suc x) = cong suc (+-right-id x)

  +-comm : ∀ x y → x + y ≈ y + x
  +-comm zero y = sym (+-right-id y)
  +-comm (suc x) y =
    begin
      suc x + y || cong suc (+-comm x y) ::
      suc y + x || sym (one-comm y x) ::
      y + suc x
    qed

    where
    one-comm : ∀ x y → x + suc y ≈ suc x + y
    one-comm zero _ = refl
    one-comm (suc x) y = cong suc (one-comm x y)

  +-suc-assoc : ∀ x y → x + suc y ≈ suc (x + y)
  +-suc-assoc x y =
    begin
      x + suc y   || sym (+-assoc x 1 y) ::
      (x + 1) + y || cong (_+ y) (+-comm x 1) ::
      suc (x + y)
    qed

  *-+-left-dist : ∀ x a b → x * (a + b) ≈ x * a + x * b
  *-+-left-dist zero a b = refl
  *-+-left-dist (suc x) a b =
    begin
      a + b + x * (a + b)       || cong ((a + b) +_) (*-+-left-dist x a b) ::
      a + b + (x * a + x * b)   || +-assoc a b _ ::
      a + (b + (x * a + x * b)) || cong (a +_) (sym (+-assoc b (x * a) (x * b))) ::
      a + (b + x * a + x * b)   || cong (a +_) (cong (_+ x * b) (+-comm b _)) ::
      a + (x * a + b + x * b)   || cong (a +_) (+-assoc (x * a) _ _) ::
      a + (x * a + (b + x * b)) || sym (+-assoc a _ _) ::
      a + x * a + (b + x * b)
    qed

  *-+-right-dist : ∀ a b x → (a + b) * x ≈ a * x + b * x
  *-+-right-dist zero b x = refl
  *-+-right-dist (suc a) b x =
    begin
      x + (a + b) * x     || cong (_+_ x) (*-+-right-dist a b x) ::
      x + (a * x + b * x) || sym (+-assoc x (a * x) (b * x)) ::
      (x + a * x) + b * x
    qed

  *-assoc : ∀ x y z → (x * y) * z ≈ x * (y * z)
  *-assoc zero y z = refl
  *-assoc (suc x) y z =
    begin
      (y + x * y) * z     || *-+-right-dist y (x * y) z ::
      y * z + (x * y) * z || cong (y * z +_) (*-assoc x y z) ::
      y * z + x * (y * z)
    qed

  *-left-id : ∀ x → 1 * x ≈ x
  *-left-id = +-right-id

  *-right-id : ∀ x → x * 1 ≈ x
  *-right-id zero = refl
  *-right-id (suc x) = cong suc (*-right-id x)

  *-right-zero : ∀ x → x * 0 ≈ 0
  *-right-zero zero = refl
  *-right-zero (suc x) = *-right-zero x

  *-comm : ∀ x y → x * y ≈ y * x
  *-comm zero y = sym (*-right-zero y)
  *-comm (suc x) zero = *-comm x zero
  *-comm (suc x) (suc y) =
    cong suc $
    begin
      y + x * suc y       || cong (y +_) (*-+-left-dist x 1 y) ::
      y + (x * 1 + x * y) || cong (λ a → y + (a + x * y)) (*-right-id x) ::
      y + (x + x * y)     || sym (+-assoc y x (x * y)) ::
      y + x + x * y       || cong2 _+_ (+-comm y x) (*-comm x y) ::
      x + y + y * x       || +-assoc x y (y * x) ::
      x + (y + y * x)     || cong (λ a → x + (a + y * x)) (sym (*-right-id y)) ::
      x + (y * 1 + y * x) || cong (x +_) (sym (*-+-left-dist y 1 x)) ::
      x + y * suc x
    qed

  suc-cong : ∀ {x y} → suc x ≈ suc y → x ≈ y
  suc-cong ≡-refl = refl
