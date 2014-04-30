module Convexity where

import System.IO
import Control.Monad
import ParseWhile
import SymEx
import Data.SBV
import Data.List
import Data.Maybe

type VarMap = [Var]
type IVarMap = [(Var, SInteger)]

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

combineConditions :: Conditions -> IVarMap ->Predicate
combineConditions xs varMap = foldr f (return $ fromBool true) xs
      where
        f = \expr sbool ->
          sbool >>= \x->
            eval expr varMap >>= \y->
              return (x &&& y)

extendConditions :: Conditions -> IVarMap -> Predicate
extendConditions xs  varMap = combineConditions ys varMap
     where
       ys = map extendCon xs

extendCon :: BExpr -> BExpr
extendCon (Not (RBinary Greater x y)) = RBinary Equality x y
extendCon (Not (RBinary Less x y)) = RBinary Equality x y
extendCon (RBinary Greater x y) = RBinary Equality x y
extendCon (RBinary Less x y) = RBinary Equality x y
extendCon x = x

inflateConditions :: Conditions -> Conditions -> Var -> IVarMap -> Predicate
inflateConditions cons1 cons2 input varMap = combineConditions (xs++ys++zs) varMap
    where 
      xs = map extendCon cons1
      ys = map (inflateCon input) cons1
      zs = map extendCon cons2

inflateCon :: Var -> BExpr -> BExpr
inflateCon input (RBinary op expr1 expr2) = (RBinary op (inflateConA input expr1) (inflateConA input expr2))
inflateCon input x = x

inflateConA :: Var -> AExpr -> AExpr
inflateConA input (Var x) = if x == input then (ABinary Add (Var x) (IntConst 1)) else (Var x)
inflateConA input (ABinary op expr1 expr2) = (ABinary op (inflateConA input expr1) (inflateConA input expr2))
inflateConA input x = x

enforceConditions :: Predicate -> Symbolic ()
enforceConditions = \x -> x >>= \y ->
      constrain y

eval :: BExpr -> IVarMap -> Symbolic SBool
eval (BoolConst x) varMap = return $ fromBool x
eval (Not expr) varMap = eval expr varMap >>= (\x -> return (bnot x))
eval (BBinary op expr1 expr2) varMap = 
         eval expr1 varMap >>= (\x ->
           eval expr2 varMap >>= (\y ->
             case op of
               And -> return (x &&& y)
               Or -> return (x ||| y)))
eval (RBinary op expr1 expr2) varMap= 
         evalA expr1 varMap >>= (\x -> 
           evalA expr2 varMap >>= (\y ->
             case op of
               Greater -> return (x.>y)
               Less -> return (x.<y)
               Equality -> return (x.==y)))

evalA :: AExpr -> IVarMap -> Symbolic SInteger
evalA (Var x) varMap =  return (varFinder x varMap)
evalA (IntConst x) varMap = return $ literal x
evalA (Neg expr) varMap = evalA expr varMap>>= (\x -> return (-1*x))
evalA (ABinary op expr1 expr2) varMap =
         evalA expr1 varMap>>= (\x -> 
           evalA expr2 varMap>>= (\y -> 
             case op of
               Add -> return (x+y)
               Subtract -> return (x-y)
               Multiply -> return (x*y)))

assignmentCCheck :: Var -> AExpr -> IVarMap -> Predicate
assignmentCCheck input expr varMap = (evalA ddx varMap) >>= (\x ->
      return (x .> -1))
      where ddx = d input (d input expr)

cCheck :: Var -> Var -> VarMap -> Execution -> IO Bool
cCheck input output varMap (conds, assignments) = 
    (model $ prove $ 
    sInteger "a" >>= (\a ->
      sInteger "b" >>= (\b ->
        sInteger "c" >>= (\c ->
          sInteger "d" >>= (\d ->
            sInteger "e" >>= (\e ->
              sInteger "f" >>= (\f ->
                sInteger "g" >>= (\g ->
                    (enforceConditions $ combineConditions conds (zip varMap (a:b:c:d:e:f:g:[])) )>>
        (assignmentCCheck input assignment (zip varMap (a:b:c:d:e:f:g:[])))))))))))>>= (\z ->
        return (isJust z))
    where
      assignment = snd $ fromJust $ find searcher assignments
      searcher = \x->fst(x) == output

cChecks :: Var -> Var -> VarMap -> ExecutionTree -> IO Bool
cChecks input output varMap xs= foldr f (return false) xs
      where
        f = \x y-> (cCheck input output varMap x) >>= (\a->
          y >>= (\b->
            return $ a || b))

executionSquare :: ExecutionTree -> [(Execution,Execution)]
executionSquare xs = [(x,y)|x<-xs, y<-xs]

assignmentECheck :: AExpr -> AExpr -> IVarMap -> Predicate
assignmentECheck expr1 expr2 varMap= 
      (evalA expr1 varMap) >>= \x ->
        (evalA expr2 varMap) >>= \y ->
          return (x .== y)

eCheck :: Var -> Var -> VarMap -> (Execution, Execution) -> IO Bool
eCheck input output varMap ((conds1, ass1),(conds2,ass2)) = 
    (model $ prove $
    sInteger "a" >>= (\a ->
      sInteger "b" >>= (\b ->
        sInteger "c" >>= (\c ->
          sInteger "d" >>= (\d ->
            sInteger "e" >>= (\e ->
              sInteger "f" >>= (\f ->
                sInteger "g" >>= (\g ->
                    (enforceConditions $ extendConditions conds (zip varMap (a:b:c:d:e:f:g:[])) )>>
                   (assignmentECheck assignment1 assignment2 (zip varMap (a:b:c:d:e:f:g:[]))))))))))) >>= (\x ->
                     return $ isJust x)
      where
        assignment1 = snd $ fromJust $ find searcher ass1
        assignment2 = snd $ fromJust $ find searcher ass2
        searcher = \x->fst(x) == output
        conds = conds1 ++ conds2

eChecks :: Var -> Var -> VarMap -> [(Execution, Execution)] -> IO Bool
eChecks input output varMap = foldr f (return false)
      where
        f = \x y -> (eCheck input output varMap x) >>= (\a->
          y >>= (\b->
            return $ a || b))

assignmentCCCheck :: Var -> AExpr -> AExpr -> IVarMap -> Predicate
assignmentCCCheck input expr1 expr2 varMap= 
      (evalA (d input expr1) varMap) >>= \x ->
        (evalA (d input expr2) varMap) >>= \y ->
          return (x .>= y)

cCCheckTest :: Var -> VarMap -> Conditions -> Conditions -> AExpr -> AExpr -> IO Bool
cCCheckTest input varMap conds1 conds2 ass1 ass2 = 
    (isVacuous $
    sInteger "a" >>= (\a ->
      sInteger "b" >>= (\b ->
        sInteger "c" >>= (\c ->
          sInteger "d" >>= (\d ->
            sInteger "e" >>= (\e ->
              sInteger "f" >>= (\f ->
                sInteger "g" >>= (\g ->
                  (enforceConditions $ inflateConditions conds1 conds2 input (zip varMap (a:b:c:d:e:f:g:[])) )>>
                    (assignmentCCCheck input ass1 ass2 (zip varMap (a:b:c:d:e:f:g:[]))))))))))) >>= (\x ->
                      return x)
 
cCCheck :: Var -> Var -> VarMap -> (Execution, Execution) -> IO Bool
cCCheck input output varMap ((conds1, ass1), (conds2, ass2)) = 
     (cCCheckTest input varMap conds1 conds2 assignment1 assignment2) >>= (\x ->
       (cCCheckTest input varMap conds2 conds1 assignment2 assignment1) >>= (\y ->
         return (x || y)))
     where
       assignment1 = snd $ fromJust $ find searcher ass1
       assignment2 = snd $ fromJust $ find searcher ass2
       searcher = \x->fst(x) == output

cCChecks :: Var -> Var -> VarMap -> [(Execution, Execution)] -> IO Bool
cCChecks input output varMap = foldr f (return false)
      where
        f = \x y -> (cCCheck input output varMap x) >>= (\a->
          y >>= (\b->
            return $ a || b))

varGenerator :: ExecutionTree -> VarMap
varGenerator xs = nub $ condVars ++ assVars
     where
       condVars = concat $ map bExprAnalyse conditions 
       assVars = concat $ map aExprAnalyse $ map snd assignments
       conditions = concat $ map fst xs
       assignments = concat $ map snd xs

varFinder :: Var -> IVarMap -> SBV Integer
varFinder x ys= snd $ fromJust $ find (\z -> (fst z)==x) ys

bExprAnalyse :: BExpr -> VarMap
bExprAnalyse (BoolConst x) = []
bExprAnalyse (Not x) = bExprAnalyse x
bExprAnalyse (BBinary op expr1 expr2) = (bExprAnalyse expr1) ++ (bExprAnalyse expr2)
bExprAnalyse (RBinary op expr1 expr2) = (aExprAnalyse expr1) ++ (aExprAnalyse expr2)

aExprAnalyse :: AExpr -> VarMap
aExprAnalyse (Var x) = [x]
aExprAnalyse (IntConst x) = []
aExprAnalyse (Neg x) = aExprAnalyse x
aExprAnalyse (ABinary op expr1 expr2) = (aExprAnalyse expr1) ++ (aExprAnalyse expr2)

convexityChecker :: Var -> Var -> ExecutionTree -> IO Bool
convexityChecker input output xs = 
     cCheckRes >>= \x ->
       eCheckRes >>= \y ->
         cCCheckRes >>= \z ->
           return (not (x || y ))
     where
       varMap = varGenerator xs
       cCheckRes = cChecks input output varMap xs
       eCheckRes = eChecks input output varMap $ executionSquare xs
       cCCheckRes = cCChecks input output varMap $ executionSquare xs

