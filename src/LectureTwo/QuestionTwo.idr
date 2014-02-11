-- --------------------------------------------------------- [ QuestionTwo.idr ]
-- Module      : LectureTwo.QuestionTwo
-- Description : More DSL Stuff
-- Copyright   : (c) Jan de Muijnck-Hughes
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module LectureTwo.QuestionTwo

-- --------------------------------------------------------------------- [ Q2a ]
--
-- This file contains a partially implemented imperative DSL.
-- Implement the functions: update; eval; and interp.

-- --------------------------------------------------------------------- [ Q2b ]
--
-- `small` is a sample program, using `dsl` notation, and any other
-- syntax overloading you find useful, make it possible to write
-- `small` as `small'`. `small'` has been commented out.

-- --------------------------------------------------------------------- [ Q2c ]
--
-- Extend `Imp` with a `for` loop construct. A possible type for this
-- construct is given below---see For. Your implementation should
-- allow for the `count` program to be written that outputs numbers in
-- the range 1 to 10. `count` has been commented out.


data Ty = TyInt | TyBool | TyUnit | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy TyUnit      = ()
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect n Ty)

  data Env : Vect n Ty -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
      stop : HasType fO (t :: G) t
      pop  : HasType k G t -> HasType (fS k) (u :: G) t

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  -- Updates the value stored at a particular position in an environment.
  update : HasType i G t -> Env G -> interpTy t -> Env G
  update = ?updateBody

  data Expr : Vect n Ty -> Ty -> Type where
       Val : interpTy a -> Expr G a
       Var : HasType i G t -> Expr G t
       Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c

  -- Evaluates an expression
  eval : Env G -> Expr G t -> interpTy t
  eval = ?evalBody

  infix 5 :=

  data Imp    : Vect n Ty -> Ty -> Type where
       Let    : Expr G t -> Imp (t :: G) u -> Imp G u
       (:=)   : HasType i G t -> Expr G t -> Imp G t
       Print  : Expr G TyInt -> Imp G TyUnit
 
       For    : Imp G i ->      -- initialise
                Imp G TyBool -> -- test
                Imp G x ->      -- increment
                Imp G t ->      -- body
                Imp G TyUnit

       (>>=)  : Imp G a -> (interpTy a -> Imp G b) -> Imp G b 
       Return : Expr G t -> Imp G t

  -- Interprets a /program/, returning a value paired with an updated
  -- environment.
  interp : Env G -> Imp G t -> IO (interpTy t, Env G)
  interp = ?interpBody

  small : Imp [] TyUnit
  small = Let (Val 42) (do Print (Var stop)
                           stop := Op (+) (Var stop) (Val 1)
                           Print (Var stop))

  -- small' : Imp [] TyUnit
  -- small' = imp (do let x = 42
  --                  Print x
  --                  x := x + 1
  --                  Print x)

  -- count : Imp [] TyUnit
  -- count = imp (do let x = 0
  --                 For (x := 0) (x < 10) (x := x + 1)
  --                     (Print (x + 1)))

  main : IO ()
  main = do interp [] small; return ()

-- --------------------------------------------------------------------- [ EOF ]
