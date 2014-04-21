module Convexity where

import System.IO
import Control.Monad
import ParseWhile
import SymEx
import Data.SBV
import Data.List
import Data.Maybe

d :: Var -> AExpr -> AExpr
d var (Var x)
        |  var == x = (IntConst 1)
        |  otherwise = (IntConst 0)
d var (IntConst x) = (IntConst 0)
d var (Neg x) = (Neg (d var x))
d var (ABinary op expr1 expr2)
        |  op == Add = (ABinary Add (d var expr1) (d var expr2))
        |  op == Subtract = (ABinary Subtract(d var expr1) (d var expr2))
        |  op == Multiply = (ABinary Add (ABinary Multiply expr1 (d var expr2)) (ABinary Multiply expr2 (d var expr1)))

model :: IO ThmResult -> IO (Maybe [Integer])
model a = a >>= \x->
      return $ extractModel x

combineConditions :: Conditions -> Predicate
combineConditions = foldr f (return $ fromBool true) 
      where
        f = \expr sbool ->
          sbool >>= \x->
            eval expr >>= \y->
              return (x &&& y)

extendConditions :: Conditions -> Predicate
extendConditions xs = combineConditions ys
     where
       ys = map extendCon xs

extendCon :: BExpr -> BExpr
extendCon (Not (RBinary Greater x y)) = RBinary Equality x y
extendCon (Not (RBinary Less x y)) = RBinary Equality x y
extendCon (RBinary Greater x y) = RBinary Equality x y
extendCon (RBinary Less x y) = RBinary Equality x y
extendCon x = x

enforceConditions :: Predicate -> Symbolic ()
enforceConditions = \x -> x >>= \y ->
      constrain y

eval :: BExpr -> Symbolic SBool
eval (BoolConst x) = return $ fromBool x
eval (Not expr) = eval expr >>= (\x -> return (bnot x))
eval (BBinary op expr1 expr2) = 
         eval expr1 >>= (\x ->
           eval expr2 >>= (\y ->
             case op of
               And -> return (x &&& y)
               Or -> return (x ||| y)))
eval (RBinary op expr1 expr2) = 
         evalA expr1 >>= (\x -> 
           evalA expr2 >>= (\y ->
             case op of
               Greater -> return (x.>y)
               Less -> return (x.<y)
               Equality -> return (x.==y)))

evalA :: AExpr -> Symbolic SInteger
evalA (Var x) = x
evalA (IntConst x) = return $ literal x
evalA (Neg expr) = evalA expr >>= (\x -> return (-1*x))
evalA (ABinary op expr1 expr2) =
         evalA expr1 >>= (\x -> 
           evalA expr2 >>= (\y -> 
             case op of
               Add -> return (x+y)
               Subtract -> return (x-y)
               Multiply -> return (x*y)))

assignmentCCheck :: Var -> AExpr -> Predicate
assignmentCCheck input expr = (evalA ddx) >>= (\x ->
      return (x .> -1))
      where ddx = d input (d input expr)

cCheck :: Var -> Var -> Execution -> IO Bool
cCheck input output (conds, assignments) = 
      newModel >>= (\x ->
        return $ isJust x)
      where
      newModel= model $ prove  $ applyConditions >>= (\_->
        (assignmentCCheck input assignment)  >>= (\y ->
          return y))
      assignment = snd $ fromJust $ find searcher assignments
      searcher = \x->fst(x) == output
      applyConditions = enforceConditions $ combineConditions conds

cChecks :: Var -> Var -> ExecutionTree -> IO Bool
cChecks input output = foldr f (return true)
      where
        f = \x y-> (cCheck input output x) >>= (\a->
          y >>= (\b->
            return $ a && b))

executionSquare :: ExecutionTree -> [(Execution,Execution)]
executionSquare xs = [(x,y)|x<-xs, y<-xs]

assignmentECheck :: AExpr -> AExpr -> Predicate
assignmentECheck expr1 expr2 = 
      (evalA expr1) >>= \x ->
        (evalA expr2) >>= \y ->
          return (x .== y)

eCheck :: Var -> Var -> (Execution, Execution) -> IO Bool
eCheck input output ((conds1, ass1),(conds2,ass2)) = 
      newModel >>= (\x ->
        return $ isJust x)
      where
        newModel = model $ prove $ applyConditions >>= \_->
          assignmentECheck assignment1  assignment2 
        assignment1 = snd $ fromJust $ find searcher ass1
        assignment2 = snd $ fromJust $ find searcher ass2
        searcher = \x->fst(x) == output
        applyConditions = enforceConditions $ extendConditions conds
        conds = reflex : (conds1 ++ conds2)
        reflex = RBinary Equality (Var "x0") (Var "x0")

eChecks :: Var -> Var -> [(Execution, Execution)] -> IO Bool
eChecks input output = foldr f (return true)
      where
        f = \x y -> (eCheck input output x) >>= (\a->
          y >>= (\b->
            return $ a && b))
