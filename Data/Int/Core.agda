-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Int.Core where

open import Agda.Builtin.Int public
  renaming (Int to ℤ)
  using (pos; negsuc)
open import Core
open import Data.Nat.Core
  renaming (_+_ to _+ℕ_;
            _*_ to _*ℕ_;
            module Props to ℕP)
  using (ℕ; suc; zero)


_-ℕ_ : ℕ → ℕ → ℤ
x -ℕ zero = pos x
zero -ℕ suc y = negsuc y
suc x -ℕ suc y = x -ℕ y

infixl 6 _-ℕ_


instance
  ℤ-Negative : Negative ℤ
  ℤ-Negative =
    record {
      Constraint = λ _ → ⊤;
      fromNeg = λ x → zero -ℕ x
    }

  ℤ-Number : Number ℤ
  ℤ-Number =
    record {
      Constraint = λ _ → ⊤;
      fromNat = λ x → pos x
    }


ℤ,≡ : Equiv ℤ
ℤ,≡ = PropEq ℤ


_+_ : ℤ → ℤ → ℤ
pos x + pos y = pos (x +ℕ y)
pos x + negsuc y = x -ℕ suc y
negsuc x + pos y = y -ℕ suc x
negsuc x + negsuc y = negsuc (suc (x +ℕ y))

infixl 6 _+_


_*_ : ℤ → ℤ → ℤ
pos x * pos y = pos (x *ℕ y)
pos zero * negsuc y = 0
pos (suc x) * negsuc y = negsuc (y +ℕ x *ℕ suc y)
negsuc x * pos zero = 0
negsuc x * pos (suc y) = negsuc (y +ℕ x *ℕ suc y)
negsuc x * negsuc y = pos (suc x *ℕ suc y)

infixl 7 _*_


module Props where
  open module MyEquiv {A : Set} = Equiv (PropEq A)

  sub-neg-zero : ∀ x → x -ℕ zero ≈ pos x
  sub-neg-zero _ = refl

  +-left-id : ∀ x → 0 + x ≈ x
  +-left-id (pos n) = refl
  +-left-id (negsuc n) = refl

  +-right-id : ∀ x → x + 0 ≈ x
  +-right-id (pos x) = cong pos (ℕP.+-right-id x)
  +-right-id (negsuc x) = refl

  +-comm : ∀ x y → x + y ≈ y + x
  +-comm (pos x) (pos y) = cong pos (ℕP.+-comm x y)
  +-comm (pos x) (negsuc y) = refl
  +-comm (negsuc x) (pos y) = refl
  +-comm (negsuc x) (negsuc y) = cong negsuc (cong suc (ℕP.+-comm x y))

  sub-sum-right : ∀ x y z → x -ℕ suc (y +ℕ z) ≈ negsuc y + (x -ℕ z)
  sub-sum-right x zero zero = refl
  sub-sum-right zero zero (suc z) = refl
  sub-sum-right (suc x) zero (suc z) = sub-sum-right x zero z
  sub-sum-right x (suc y) zero = cong (λ a → x -ℕ suc (suc a)) (ℕP.+-right-id y)
  sub-sum-right zero (suc y) (suc z) = cong negsuc (cong suc (ℕP.+-suc-assoc y z))
  sub-sum-right (suc x) (suc y) (suc z) =
    begin
      x -ℕ suc (y +ℕ suc z)     || cong (x -ℕ_) (cong suc (ℕP.+-suc-assoc y z)) ::
      x -ℕ suc (suc y +ℕ z)     || sub-sum-right x (suc y) z ::
      negsuc (suc y) + (x -ℕ z)
    qed

  sub-sum-left : ∀ x y z → (x +ℕ y) -ℕ z ≈ pos x + (y -ℕ z)
  sub-sum-left zero y z = sym (+-left-id (y -ℕ z))
  sub-sum-left (suc x) y zero = refl
  sub-sum-left (suc x) zero (suc z) = cong (_-ℕ z) (ℕP.+-right-id x)
  sub-sum-left (suc x) (suc y) (suc z) =
    begin
      (x +ℕ suc y) -ℕ z      || cong (_-ℕ z) (ℕP.+-suc-assoc x y) ::
      suc (x +ℕ y) -ℕ z      || sub-sum-left (suc x) y z ::
      pos (suc x) + (y -ℕ z)
    qed

  +-assoc : ∀ x y z → (x + y) + z ≈ x + (y + z)
  +-assoc (pos x) (pos y) (pos z) = cong pos (ℕP.+-assoc x _ _)
  +-assoc (pos x) (pos y) (negsuc z) = sub-sum-left x y (suc z)
  +-assoc (pos x) (negsuc y) (pos z) =
    begin
      (x -ℕ suc y) + pos z || +-comm (x -ℕ suc y) (pos z) ::
      pos z + (x -ℕ suc y) || sym (sub-sum-left z x (suc y)) ::
      (z +ℕ x) -ℕ suc y    || cong (_-ℕ suc y) (ℕP.+-comm z x) ::
      (x +ℕ z) -ℕ suc y    || sub-sum-left x z (suc y) ::
      pos x + (z -ℕ suc y)
    qed
  +-assoc (pos x) (negsuc y) (negsuc z) =
    begin
      x -ℕ suc y + negsuc z   || +-comm (x -ℕ suc y) (negsuc z) ::
      negsuc z + (x -ℕ suc y) || sym (sub-sum-right x z (suc y)) ::
      x -ℕ (suc z +ℕ suc y)   || cong (x -ℕ_) (ℕP.+-comm (suc z) (suc y)) ::
      x -ℕ (suc y +ℕ suc z)   || cong (x -ℕ_) (cong suc (ℕP.+-suc-assoc y z)) ::
      x -ℕ suc (suc (y +ℕ z))
    qed
  +-assoc (negsuc x) (pos y) (pos z) =
    begin
      (y -ℕ suc x) + pos z || +-comm (y -ℕ suc x) (pos z) ::
      pos z + (y -ℕ suc x) || sym (sub-sum-left z y (suc x)) ::
      (z +ℕ y) -ℕ suc x    || cong (_-ℕ suc x) (ℕP.+-comm z y) ::
      (y +ℕ z) -ℕ suc x
    qed
  +-assoc (negsuc x) (pos y) (negsuc z) =
    begin
      y -ℕ suc x + negsuc z   || +-comm (y -ℕ suc x) (negsuc z) ::
      negsuc z + (y -ℕ suc x) || sym (sub-sum-right y z (suc x)) ::
      y -ℕ (suc z +ℕ suc x)   || cong (y -ℕ_) (ℕP.+-comm (suc z) (suc x)) ::
      y -ℕ (suc x +ℕ suc z)   || sub-sum-right y x (suc z) ::
      negsuc x + (y -ℕ suc z)
    qed
  +-assoc (negsuc x) (negsuc y) (pos zero) = refl
  +-assoc (negsuc x) (negsuc y) (pos (suc z)) = sub-sum-right z x y
  +-assoc (negsuc x) (negsuc y) (negsuc z) =
    cong negsuc $ cong suc $
    begin
      suc ((x +ℕ y) +ℕ z) || cong suc (ℕP.+-assoc x y z) ::
      suc (x +ℕ (y +ℕ z)) || sym (ℕP.+-suc-assoc x (y +ℕ z)) ::
      x +ℕ (suc (y +ℕ z))
    qed

  *-left-id : ∀ x → 1 * x ≈ x
  *-left-id (pos x) = cong pos (ℕP.+-right-id x)
  *-left-id (negsuc x) = cong negsuc (ℕP.+-right-id x)

  *-right-id : ∀ x → x * 1 ≈ x
  *-right-id (pos x) = cong pos (ℕP.*-right-id x)
  *-right-id (negsuc x) =
    cong negsuc (trans (ℕP.*-comm x 1) (ℕP.+-right-id x))

  *-assoc : ∀ x y z → (x * y) * z ≈ x * (y * z)
  *-assoc (pos x) (pos y) (pos z) = cong pos (ℕP.*-assoc x y z)
  *-assoc (pos zero) (pos zero) (negsuc z) = refl
  *-assoc (pos zero) (pos (suc y)) (negsuc z) = refl
  *-assoc (pos (suc x)) (pos zero) (negsuc z) =
    begin
      pos (x *ℕ 0) * negsuc z || cong (λ a → pos a * negsuc z) (ℕP.*-right-zero x) ::
      pos 0 * negsuc z        || cong pos (sym (ℕP.*-right-zero x)) ::
      pos (x *ℕ 0)
    qed
  *-assoc (pos (suc x)) (pos (suc y)) (negsuc z) =
    cong negsuc $ ℕP.suc-cong $
    ℕP.*-assoc (suc x) (suc y) (suc z)
  *-assoc (pos zero) (negsuc y) (pos zero) = refl
  *-assoc (pos zero) (negsuc y) (pos (suc z)) = refl
  *-assoc (pos (suc x)) (negsuc y) (pos zero) = cong pos (sym (ℕP.*-right-zero x))
  *-assoc (pos (suc x)) (negsuc y) (pos (suc z)) =
    cong negsuc $ ℕP.suc-cong $
    ℕP.*-assoc (suc x) (suc y) (suc z)
  *-assoc (pos zero) (negsuc y) (negsuc z) = refl
  *-assoc (pos (suc x)) (negsuc y) (negsuc z) = cong pos (ℕP.*-assoc (suc x) (suc y) (suc z))
  *-assoc (negsuc x) (pos zero) (pos z) = refl
  *-assoc (negsuc x) (pos (suc y)) (pos zero) = cong (λ a → negsuc x * pos a) (sym (ℕP.*-right-zero y))
  *-assoc (negsuc x) (pos (suc y)) (pos (suc z)) =
    cong negsuc $ ℕP.suc-cong $
    ℕP.*-assoc (suc x) (suc y) (suc z)
  *-assoc (negsuc x) (pos zero) (negsuc z) = refl
  *-assoc (negsuc x) (pos (suc y)) (negsuc z) = cong pos (ℕP.*-assoc (suc x) (suc y) (suc z))
  *-assoc (negsuc x) (negsuc y) (pos zero) = cong pos (ℕP.*-right-zero (y +ℕ x *ℕ suc y))
  *-assoc (negsuc x) (negsuc y) (pos (suc z)) = cong pos (ℕP.*-assoc (suc x) (suc y) (suc z))
  *-assoc (negsuc x) (negsuc y) (negsuc z) =
    cong negsuc $ ℕP.suc-cong $
    ℕP.*-assoc (suc x) (suc y) (suc z)

  *-comm : ∀ x y → x * y ≈ y * x
  *-comm (pos x) (pos y) = cong pos (ℕP.*-comm x y)
  *-comm (pos zero) (negsuc y) = refl
  *-comm (pos (suc x)) (negsuc y) = cong negsuc (ℕP.suc-cong (ℕP.*-comm (suc x) (suc y)))
  *-comm (negsuc x) (pos zero) = refl
  *-comm (negsuc x) (pos (suc y)) = cong negsuc (ℕP.suc-cong (ℕP.*-comm (suc x) (suc y)))
  *-comm (negsuc x) (negsuc y) = cong pos (ℕP.*-comm (suc x) (suc y))

  -- *-+-left-dist : ∀ x a b → x * (a + b) ≈ x * a + x * b
  -- *-+-left-dist (pos x) (pos a) (pos b) = cong pos (ℕP.*-+-left-dist x a b)
  -- *-+-left-dist (pos x) (pos a) (negsuc b) = {!!}
  -- *-+-left-dist (pos x) (negsuc a) (pos b) = {!!}
  -- *-+-left-dist (pos x) (negsuc a) (negsuc b) = {!!}
  -- *-+-left-dist (negsuc x) (pos a) (pos b) = {!!}
  -- *-+-left-dist (negsuc x) (pos a) (negsuc b) = {!!}
  -- *-+-left-dist (negsuc x) (negsuc a) (pos b) = {!!}
  -- *-+-left-dist (negsuc x) (negsuc a) (negsuc b) = {!!}