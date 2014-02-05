-- ---------------------------------------------------------- [ LectureOne.idr ]
-- Module      : LectureTwo
-- Description : Exercises for Lecture Two
-- Copyright   : (c) The Idris Community 2014
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module LectureTwo

-- -------------------------------------------------------------- [ Question 8 ]
--
-- Add a let binding construct to the Expr language, and extend
-- the interp function and dsl notation to handle it.
  

-- -------------------------------------------------------------- [ Question 9 ]
--
-- In L2-imp.idr you will ﬁnd a partially implemented imperative DSL.
-- Implement the following missing functions:


-- --------------------------------------------------------------------- [ Q9a ]
-- update : HasType i G t -> Env G -> interpTy t -> Env G, which updates
-- the value stored at a particular position in an environment.

-- --------------------------------------------------------------------- [ Q9b ]
-- eval : Env G -> Expr G t -> interpTy t, which evaluates an expression
--

-- --------------------------------------------------------------------- [ Q9c ]
-- interp : Env G -> Imp G t -> IO (interpTy t, Env G), which interprets
-- a program, returning a value paired with an updated environment.



-- -------------------------------------------------------------- [ Question 10 ]
--
-- One example program is the following:
--

small : Imp [] TyUnit
small = Let (Val 42) (do Print (Var stop)
                      stop := Op (+) (Var stop) (Val 1)
                      Print (Var stop))

--
-- Using dsl notation, and any other syntax overloading you ﬁnd useful,
-- make it possible to write small as follows:

small : Imp [] TyUnit
small = imp (do let x = 42
                Print x
                x := x + 1
                Print x)


-- -------------------------------------------------------------- [ Question 11 ]
--
-- Extend Imp with a for loop construct. One possible type for this is:
--
-- For : Imp G i -> -- initialise
--       Imp G TyBool -> -- test
--       Imp G x -> -- increment
--       Imp G t -> -- body
--       Imp G TyUnit

-- Your implementation should allow the following program to be written,
-- which outputs numbers from 1 to 10:
--
-- count : Imp [] TyUnit
-- count = imp (do let x = 0
--                 For (x := 0) (x < 10) (x := x + 1)
--                 (Print (x + 1)))



