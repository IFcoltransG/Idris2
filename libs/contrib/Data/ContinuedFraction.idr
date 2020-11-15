module Data.ContinuedFraction
import Data.Nat
import Data.Maybe
%default total
--TODO
--Define helper functions
--Create instances
--Rename and simplify (ensuring nice line length) ('full', 'ingest', 'egest')
--rewrite supporting negatives
--Documentation and comments
--Proofs
--Linearity (e.g. in reversing)

infixl 8 |-|
-- positive difference between Nats
(|-|) : Nat -> Nat -> Nat
x |-| Z = x
Z |-| x = x
(S x) |-| (S y) = x |-| y

natDiv : Nat -> Nat -> Maybe Nat
natDiv _ Z = Nothing
natDiv Z _ = Just Z
natDiv x y = if x < y
  then Just Z
  else do
    let diff = assert_smaller x $ x |-| y
    div <- diff `natDiv` y --29
    pure $ S div

data ContFrac : Type where
  Nil : ContFrac --represents ±infinite number
  (::) : Nat -> Inf (ContFrac) -> ContFrac

{-
--a continued fraction that repeats a list of values
covering repeatedContFrac : List Nat -> ContFrac
repeatedContFrac xs = repeat xs xs where
  repeat ys []        = repeat ys ys
repeat ys (z :: zs) = z :: (Delay $ repeat ys zs) -}

floor : ContFrac -> ContFrac
floor Nil = Nil
floor (head :: _) = [head]

maybePairDiv : (Nat, Nat) -> Maybe Nat
maybePairDiv (_, Z) = Nothing
maybePairDiv (x, (S y)) = Just $ divNatNZ x (S y) absurd

rationalToContFrac : (Nat, Nat) -> ContFrac
rationalToContFrac rational@(numer, denom) = case maybePairDiv rational of
  Just ratio => ratio :: rationalToContFrac (denom, (numer |-| ratio * denom)) -- could be non-smaller
  Nothing => []

contFracToRational : ContFrac -> (Nat, Nat)
contFracToRational [] = (1, 0)
contFracToRational (x :: xs) =
  let (num, denom) = (contFracToRational $ assert_smaller (x :: xs) xs)
  in (x*num + denom, num)

simplifyRational : (Nat, Nat) -> (Nat, Nat)
simplifyRational (_, Z) = (1, 0)
simplifyRational (a, (S b)) = fromMaybe (1, 0) $ do
  let factor = gcd a (S b)
  a' <- a `natDiv` factor
  b' <- (S b) `natDiv` factor
  pure (a', b')

contFracIgnoresSimplification : (x, y : Nat) ->
  (rationalToContFrac (x, y) = rationalToContFrac (simplifyRational (x, y)))
contFracIgnoresSimplification _ Z = Refl
contFracIgnoresSimplification x (S y) = ?ignores_2

contFracSimplestForm : (cf : ContFrac) ->
  (contFracToRational cf = simplifyRational (contFracToRational cf))
contFracSimplestForm [] = Refl
contFracSimplestForm (k :: x) = ?simple_3

rationalsCanonical : (x, y : Nat) -> (
  contFracToRational (rationalToContFrac (x, y)) =
  simplifyRational (x, y))
rationalsCanonical x Z = Refl
rationalsCanonical x (S y) = ?holeS

{-
namespace Homography
  --represents a function (ax + b)/(cx + d)
  Homographic : Type -> Type
  Homographic n = (n, n,
                    n, n)

  --take the first term from a contfrac and simplify it into a homography
  --hopefully reducing error bounds
  absorb : Num n => Homographic n -> n -> Homographic n
  absorb (a, b, c, d) x = (a*x + b, a, c*x + d, c)

  --extracts a known first term from a homography if possible
  --if a/c = b/d then first term of applying that hom is a/b
  --(assuming c != 0, d != 0)
  --because (ax+a)/(cx+c) = a/c no matter what x is (by factoring (x+1) out)
  --i.e. after increasing precision enough, the bounds of the hom will be
  --between two consecutive integers for any x.
  --also assumes continued fraction terms are positive
  tryEmit : (Eq n, Integral n) => Homographic n -> Maybe n
  tryEmit (a, b, c, d) = do
    let pairs = [(a, c), (b, d)]
    let pairs' = the (List (n, n)) $ filter (/= (0, 0)) $ pairs
    divisions <- sequence $ map maybePairDiv pairs'
    case divisions of
      [] => Nothing
      (x :: xs) => toMaybe (all (== x) xs) x

  --gives homography for second term after emitting a known first term
  emit : (Neg n) => Homographic n -> n -> Homographic n
  emit (a, b, c, d) x = (c, d, a - c*x, b - d*x)

  --computes (ax + b)/(cx + d)
  --if a term can be deduced from the homography alone, then does that
  --otherwise takes a term from the continued fraction
  --and evaluates the homography on it
  --so as to make the bounds on the homography smaller
  --(and hopefully get a single possible integer)
  --then repeats for as many terms as necessary
  covering homography : (Abs n, Neg n, Ord n, Integral n) => Homographic n -> ContFrac n -> ContFrac n
  homography hom@(a, b, c, d) frac = case (c, d) == (0, 0) of
      True => []
      False => case (tryEmit hom) of
        Just y => y :: homography (emit hom y) frac
        Nothing => case frac of
          [] => if abs a > abs c then [] else [0]
          [x] => rationalToContFrac (a*x + b, c*x + d)
          (x :: xs) => homography (absorb hom x) xs

  --multiply a continued fraction by x
  covering scalarMul : (Abs n, Neg n, Ord n, Integral n) => n -> ContFrac n -> ContFrac n
  scalarMul x = homography (x, 0, 0, 1)

  covering scalarDiv : (Abs n, Neg n, Ord n, Integral n) => n -> ContFrac n -> ContFrac n
  scalarDiv x = homography (1, 0, 0, x)


namespace Bihomography
  --represents a function (axy + bx + cy + d)/(exy + fx + gy + h)
  Bihomographic : Type -> Type
  Bihomographic n = (n, n, n, n,
                      n, n, n, n)

  --(reverseBihomography bihom) on x and y = bihom on y and x
  reverseBihomography : Bihomographic n -> Bihomographic n
  reverseBihomography (a, b, c, d, e, f, g, h) = (a, c, b, d, e, g, f, h)

  --takes a value from the second contfrac
  --and simplifies it into the homography
  rightAbsorb : (Num n) => n -> Bihomographic n -> Bihomographic n
  rightAbsorb y (a, b, c, d, e, f, g, h) = (a*y+b, a, c*y+d, c, e+y+f, e, g*y+h, g)

  --like RightAbsorb, but flips the bihomography before and after
  --(taking from the first contfrac, effectively)
  leftAbsorb : (Num n) => n -> Bihomographic n -> Bihomographic n
  leftAbsorb y bihom = reverseBihomography $ rightAbsorb y (reverseBihomography bihom)

  norms : (Ord n, Integral n, Neg n, Abs n) => Bihomographic n -> n -> n -> (Maybe n, Maybe n)
  norms (a, b, c, d, e, f, g, h) x y = MkPair (
      do
        base <- map abs $ maybePairDiv (d, h)
        xAbsolute <- map abs $ maybePairDiv (b, f)
        pure . abs $ base - xAbsolute
    ) (
      do
        base <- map abs $ maybePairDiv (d, h)
        yAbsolute <- map abs $ maybePairDiv (c, g)
        pure . abs $ base - yAbsolute
    )

  --decide where to absorb from
  chooseSide : (Ord n, Integral n, Neg n, Abs n) => Bihomographic n -> n -> n -> (Lazy t -> Lazy t -> t)
  chooseSide bihom x y = case norms bihom x y of
      (Nothing, _) => chooseY
      (Just _, Nothing) => chooseX
      (Just xDif, Just yDif) => if xDif > yDif then chooseX else chooseY
    where chooseX : (Lazy t -> Lazy t -> t)
          chooseX = \x, y => x
          chooseY : (Lazy t -> Lazy t -> t)
          chooseY = \x, y => y

  --either right absorb or left absorb
  absorb : (Ord n, Integral n, Neg n, Abs n) => Bihomographic n -> n -> n -> Bihomographic n
  absorb bihom x y = (chooseSide bihom x y) (leftAbsorb x) (rightAbsorb y) $ bihom

  --first term is between a/e, b/f, c/g, and d/h
  --so if floor of all is ==, that is first term
  tryEmit : (Eq n, Integral n) => Bihomographic n -> Maybe n
  tryEmit (a, b, c, d, e, f, g, h) = do
    let pairs = [(a, e), (b, f), (c, g), (d, h)]
    let pairs' = the (List (n, n)) $ filter (/= (0, 0)) $ pairs
    divisions <- sequence $ map maybePairDiv pairs'
    case divisions of
      [] => Nothing
      (x :: xs) => toMaybe (all (== x) xs) x

  emit : (Neg n) => Bihomographic n -> n -> Bihomographic n
  emit (a, b, c, d, e, f, g, h) x = (e, f, g, h, a-e*x, b-f*x, c-g*x, d-h*x)

  covering bihomography : (Abs n, Neg n, Abs n, Ord n, Integral n) => Bihomographic n -> ContFrac n -> ContFrac n -> ContFrac n
  bihomography bihom@(a, b, c, d, e, f, g, h) x y = case (e, f, g, h) == (0, 0, 0, 0) of
    True => [] -- division by zero
    False => case (tryEmit bihom) of
      Just z => z :: bihomography (emit bihom z) x y --first term can only be z; finding next terms from there
      Nothing => case (x, y) of
        ([], rs) => homography (a, c, e, g) rs -- only absorb from right
        ([q], rs) => homography (q*a + c, q*b + d, q*e + g, q*f + h) rs -- simplify an exact value q into bihom
        (_, []) => bihomography (reverseBihomography bihom) y x -- flip x and y
        (_, [r]) => bihomography (reverseBihomography bihom) y x -- flip x and y
        ((q :: qs), (r :: rs)) => let side = (chooseSide bihom q r)
      in uncurry (bihomography (absorb bihom q r)) $ (side (qs, r :: rs) (q :: qs, rs)) -- is right?

{-
covering implementation (Integral n, Neg n, Ord n, Abs n) => Num (ContFrac n) where
  (+) = bihomography (0, 1, 1, 0, 0, 0, 0, 1)
  (*) = bihomography (1, 0, 0, 0, 0, 0, 0, 1)
  fromInteger n = [fromInteger n]


implementation Fractional IContFrac where
  (/) = bihomography ()

  recip (0 :: xs) = xs
  recip xs        = 0 :: xs-}
-- figure out what things mustn't be negative?

--debug show, rather than as fraction x/y {-}
Show (ContFrac) where
  show [] = "[]"
  show [x] = "[" ++ show x ++ "]"
  show (x :: xs) = "[" ++ show x ++ "; " ++ showListed xs ++ "]"
    where showListed [] = ""
          showListed [x] = show x
          showListed (x :: xs) = show x ++ ", " ++ showListed (assert_smaller (x :: xs) xs)

{-} -}
