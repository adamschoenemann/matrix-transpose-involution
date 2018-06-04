module Matrix3
-- This is a proof that matrix transposition is an involution, i.e. that
-- m = transpose (transpose m) 
-- This is exactly copied from the Agda proof that you can find online

-- import vector into scope
import Data.Vect

-- hide default vector transpose implementation
-- The default implementation will not work with this proof, as it uses zipWith instead of map, head and tail
%hide transpose

-- check all functions for totality
%default total

foo : Nat -> Nat
foo x = ?rhs

-- A matrix is just a 2d vector
-- The dimensions are rows-first (height)
-- The implementation is column-first, so [[1,2,3],[4,5,6]] corresponds to the matrix
-- | 1 4 |
-- | 2 5 |
-- | 3 6 |
Matrix : Nat -> Nat -> Type -> Type
Matrix r c a = Vect c (Vect r a)
  
scalarMult : Int -> Matrix m n Int -> Matrix m n Int
scalarMult x [] = []
scalarMult x (y :: xs) = map (*x) y :: scalarMult x xs

-- A function that models congruence for functions with 2 parameters:
-- If we know that (a = c) and (b = d) then (f a b = f c d)
cong2 : { A, B, C : Type } -> { f : A -> B -> C } -> { a, c : A } -> { b, d : B } -> 
        (a = c) -> (b = d) -> f a b = f c d
cong2 Refl Refl = Refl


-- transpose a matrix!
transpose : Matrix h w a -> Matrix w h a
transpose {h = Z} x = [] -- a matrix with zero height transposed has zero width (no columns)
-- take the first of each column, and make this the new left-most column 
-- prepended to the transpose of the tail of each column
transpose {h = (S k)} x = map head x :: (transpose (map tail x))


-- this lemma states that the transpose of a matrix m is equal to the tail of each column in
-- the transpose of (c :: m), where c is some column vector of the same height as m
-- basically, this means that if we have a matrix (c :: m) and transpose it, then if we take
-- the tail of each column in that matrix, it is the same as simply transposing m
-- Example:
-- m = [[2,5,8],[3,6,9]], c = [1,4,7]
-- transpose m = [[2,3],[5,6],[8,9]]
-- (c :: m) = [[1,3,7],[2,5,8],[3,6,9]]
-- transpose (c :: m) = [[1,2,3],[4,5,6],[7,8,9]]
-- map tail (transpose c :: m) = [[2,3],[5,6],[8,9]]
-- You can see that it is the same as simply (transpose m)
lem1 : (c : Vect h a) -> (m : Matrix h w a) -> transpose m = map Vect.tail (transpose (c :: m))
lem1 {h = Z} c m = Refl
lem1 {h = (S k)} (x :: c) m = cong {f = ((map Vect.head m) ::)} (lem1 c (map Vect.tail m))

map_def_2 : {xs : List t} -> map f (x :: xs) = f x :: map f xs
map_def_2 = Refl


-- this lemma states that a column c is the same as the head of head column of the transpose of a matrix
-- consisting of (c :: m).
-- That is, if you have a matrix (c :: m), then the head of each column of its transpose is c
-- Alternatively, the first column of a matrix is the head of every column of its transpose
lem2 : (c : Vect h a) -> (m : Matrix h w a) -> c = map Vect.head (transpose (c :: m))
lem2 {h = Z} [] m = Refl
lem2 {h = (S k)} (x :: c) m = cong {f = ((::) x)} (lem2 c (map tail m))

-- Now, we put our lemmas together
-- The first case is trivial
-- The second case, not so much
-- Starting from outside-in, we first employ a proof using transitivity, i.e. (a = b) -> (b = c) -> (a = c)
-- `trans` needs two proofs.
-- The first proof uses congruence which is (a = b) -> (f a = f b)
--    This means that, by induction we prove that transpose_involution holds for xs, which is the matrix without
--    its first column. Thus, we proved that xs = transpose (transpose xs)
--    We then use congruence to obtain a proof that prepending x to xs does not change this fact
--    Thus, prf1 : x :: xs = x :: transpose (transpose xs)
-- This gave us the (a = b) part of transitivity, now we need to prove that (b = c) in order to prove that (a = c)
-- In our case, a is (x :: xs), b is (x :: transpose (transpose xs)), and d should be (transpose (transpose (x :: xs)))
-- If we can get this d, mentioned above, then we're done
-- The second proof, which we call "d", uses congruence for functions of arity 2
--    First, we use lem2 to prove that the column x is the head of each column of the transpose of (x :: xs)
--    Then we use congruence of transpose and lem1 to obtain the second proof of equality
--    Thus, b_c : f x (transpose (transpose xs)) = f (head (transpose (x :: xs))) (transpose (tail (transpose (x :: xs))))
--       where f : Vect h a -> Vect k (Vect h a) -> Vect (S k) (Vect h a)
--    TODO: More, and better explanation
transpose_involution : (m : Matrix h w a) -> m = transpose (transpose m)
transpose_involution [] = Refl
transpose_involution (x :: xs) =
  let a_b = (cong {f = (x ::)} (transpose_involution xs))
      b_c_subproof1 = lem2 x xs 
      b_c_subproof2 = (cong {f = transpose} (lem1 x xs))
      b_c = cong2 {f = (::)} b_c_subproof1 b_c_subproof2
  in  trans a_b b_c
