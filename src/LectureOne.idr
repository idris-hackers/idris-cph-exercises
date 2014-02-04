-- ---------------------------------------------------------- [ LectureOne.idr ]
-- Module      : LectureOne
-- Description : Exercises for Lecture One
-- Copyright   : (c) The Idris Community 2014
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module LectureOne

-- -------------------------------------------------------------- [ Question 1 ]
--
-- Implement the following function which constructs a vector that
-- contains n copies of a given item.

vrepeat : (n : Nat) -> a -> Vect n a
vrepeat = ?repeatBody

-- -------------------------------------------------------------- [ Question 2 ]
--
-- Implement the following functions.
--
-- Do the types tell you enough to suggest what they should do?
--
vtake : (n : Nat) -> Vect (n + m) a -> Vect n a
vtake = ?takeBody

vdrop : (n : Nat) -> Vect (n + m) a -> Vect m a
vdrop = ?dropBody

-- -------------------------------------------------------------- [ Question 3 ]
--
-- A matrix is a 2-dimensional vector, and could be defined as follows:
--
Matrix :  Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

-- --------------------------------------------------------------------- [ Q3a ]
-- Using vrepeat (above) and Vect.zipWith, write a function which
-- transposes a matrix.
--
-- Hints: Remember to think carefully about its type first! zipWith
-- for vectors is defined as follows:
--
--    zipWith : (a -> b -> c) -> Vect a n -> Vect b n -> Vect c n
--    zipWith f []      []      = []
--    zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
--

-- --------------------------------------------------------------------- [ Q3b ]
--
-- Write a function to multiply two matrices.


-- ---------------------------------------------------------------------- [ Q4 ]
--
-- The following view describes a pair of numbers as a difference:
--
data Cmp : Nat -> Nat -> Type where
  cmpLT : (y : _) -> Cmp x (x + S y)
  cmpEQ : Cmp x x
  cmpGT : (x : _) -> Cmp (y + S x) y

-- --------------------------------------------------------------------- [ Q4a ]
--
-- Implement the following function which proves that every pair of
-- numbers can be expressed in this way.

-- Hint: recall parity from the lecture. You will find the with
-- construct very useful!
--
cmp : (n:Nat) -> (m:Nat) -> Cmp n m
cmp = ?cmpBody

-- --------------------------------------------------------------------- [ Q4b ]
--
-- Assume you have a vector xs : Vect a n, where n is unknown. How
-- could you use cmp to construct a suitable input to vtake and vdrop
-- from xs?

-- ---------------------------------------------------------------------- [ Q5 ]
--
-- Implement the following functions:
--
plus_nSm : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
plus_nSm = ?plus_nSmBody

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes = ?plus_commutesBody

plus_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) ->
             n + (m + p) = (n + m) + p
plus_assoc = ?plus_assocBody

-- ---------------------------------------------------------------------- [ Q6 ]
--
-- One way to define a reverse function for lists is as follows:

reverse : List a -> List a
reverse xs = revAcc [] xs
             where
               revAcc : List a -> List a -> List a
               revAcc acc [] = acc
               revAcc acc (x :: xs) = revAcc (x :: acc) xs

-- Write the equivalent function for vectors.
--
-- Hint: You can use the same structure as the definition for List,
-- but you will need to think carefully about the type for revAcc, and
-- may need to do some theorem proving.

vreverse : Vect a n -> Vect a n
vreverse = ?vreverseBody

-- ---------------------------------------------------------------------- [ Q7 ]
--
-- You are given the following definition of binary trees:

data Tree a = Leaf | Node (Tree a) a (Tree a)

-- Define a membership predicate ElemTree and a function elemInTree
-- which calculates whether a value is in the tree, and a
-- corresponding proof.

data ElemTree : a -> Tree a -> Type where
  {} -- constructors

elemInTree : DecEq a => (x : a) -> (t : Tree a) -> Maybe (ElemTree x t)
elemInTree = ?elemInTreeBody

-- --------------------------------------------------------------------- [ EOF ]
