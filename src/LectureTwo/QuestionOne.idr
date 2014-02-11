-- --------------------------------------------------------- [ QuestionOne.idr ]
-- Module      : Lecture2.QuestionOne
-- Description : Extending Expr DSL
-- Copyright   : (c) The Idris Community
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module LectureTwo.QuestionOne

-- This is an interpreter for the simply typed \lambda-calculus. Add a
-- let binding construct to the language, and extend the `interp`
-- function and dsl notation to handle it.

-- Data Types for our object language: The Simply Typed \lambda-Calculus
data Ty = TyInt
        | TyBool
        | TyFun Ty Ty

-- Translate the object language types into the meta language types
interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect n Ty) -- G is the vector of types for all of our local variables.

  -- Environment is a heterogeneous list where every element in the
  -- list has a possibly different type determined by the elements of
  -- another list.
  data Env : Vect n Ty -> Type where
       Nil  : Env Nil
       (::) : interpTy a -> Env G -> Env (a :: G)

  -- The `HasType` is used to help determine if a type exists.
  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
       stop : HasType fO (t :: G) t
       pop  : HasType k G t -> HasType (fS k) (u :: G) t

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  -- The expressions from the simply typed \lambda calculus.
  data Expr : Vect n Ty -> Ty -> Type where
      Var : HasType i G t -> Expr G t
      Val : (x : Int) -> Expr G TyInt
      Lam : Expr (a :: G) t -> Expr G (TyFun a t)
      App : Expr G (TyFun a t) -> Expr G a -> Expr G t
      Op  : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b -> 
            Expr G c
      If  : Expr G TyBool -> Expr G a -> Expr G a -> Expr G a
  -- Your let binding goes here.
 
  -- The DSL for the simply typed \lambda calculus
  dsl expr
      lambda      = Lam
      variable    = Var
      index_first = stop
      index_next  = pop
  -- Your let binding goes here.

  -- Function application
  (<$>) : |(f : Expr G (TyFun a t)) -> Expr G a -> Expr G t
  (<$>) = \f, a => App f a

  pure : Expr G a -> Expr G a
  pure = id

  syntax IF [x] THEN [t] ELSE [e] = If x t e

  (==) : Expr G TyInt -> Expr G TyInt -> Expr G TyBool
  (==) = Op (==)

  (<) : Expr G TyInt -> Expr G TyInt -> Expr G TyBool
  (<) = Op (<)

  -- Arithmetic in the Simply Typed \lambda calculus
  instance Num (Expr G TyInt) where
    (+) x y = Op (+) x y
    (-) x y = Op (-) x y
    (*) x y = Op (*) x y

    abs x = IF x < 0 THEN (-x) ELSE x

    fromInteger = Val . fromInteger
  
  -- The interpreter for the Simply Typed \lambda calculus
  total interp : Env G -> Expr G t -> interpTy t
  interp env (Var i)     = lookup i env
  interp env (Val x)     = x
  interp env (Lam sc)    = \x => interp (x :: env) sc
  interp env (App f s)   = interp env f (interp env s)
  interp env (Op op x y) = op (interp env x) (interp env y)
  interp env (If x t e)  = if interp env x then interp env t 
                                           else interp env e
  -- Identity
  eId : Expr G (TyFun TyInt TyInt)
  eId = expr (\x => x)

  -- Test
  eTEST : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eTEST = expr (\x, y => y)

  -- Addition
  eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eAdd = expr (\x, y => x + y)

  -- Doubling
  eDouble : Expr G (TyFun TyInt TyInt)
  eDouble = expr (\x => [| eAdd x x |])

  -- Factorial
  fact : Expr G (TyFun TyInt TyInt)
  fact = expr (\x => IF x == 0 THEN 1 ELSE [| fact (x - 1) |] * x)

testFac : Int
testFac = interp [] fact 4

unitTestFac : so (interp [] fact 4 == 24)
unitTestFac = oh

main : IO ()
main = do
  putStr "Enter a number: "
  n <- getLine
  putStrLn ("Answer: " ++ show (interp [] fact (cast n)))
                                                                                          
