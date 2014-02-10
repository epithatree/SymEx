module SymEx where

import System.IO
import Control.Monad
import ParseWhile

type Var = String

type Condition = BExpr
type Assignment = (Var, AExpr)

type Conditions = [Condition]
type Assignments = [Assignment]

type Execution = (Conditions, Assignments)
type ExecutionTree = [Execution]

execute :: Stmt -> ExecutionTree
execute stmt = reduce stmt ([],[])

restructure :: Stmt -> [Stmt]
restructure (Seq xs) = xs
restructure xs = [xs]

reduce :: Stmt -> Execution -> [Execution]
reduce (Seq xs) exec = foldl (\x y -> concat(map (reduce y) x))  [exec] xs
reduce (Assign string expr) exec = [update string expr exec]
reduce (If expr stmta stmtb) exec = let (conditions, assignments) = exec
                                        (newexpr, newassign) = insertb expr assignments
                                    in reduce stmta ((newexpr:conditions),newassign)++(reduce stmtb ((Not newexpr:conditions),newassign))
reduce Skip exec = [exec]
reduce (While expr stmt) exec = error "while not supported"

update :: Var -> AExpr -> Execution -> Execution
update var expr exec = let (conditions, assignments) = exec
                       in  (conditions, (replace var (insert expr assignments)))

insert :: AExpr -> Assignments -> (AExpr, Assignments)
insert (Var x) ys
        | null z = (Var (x++"0"), (x, Var (x++"0")):ys)
        | otherwise =  (snd (head z), ys)
       where z = filter (\u -> x==(fst u)) ys
insert (IntConst x) y = (IntConst x, y)
insert (Neg x) y = (\(s,t)->(Neg s,t)) (insert x y)
insert (ABinary op expr1 expr2) ass = ((ABinary op aexpr bexpr), bass)
                                    where (aexpr, aass) = (insert expr1 ass)
                                          (bexpr, bass) = (insert expr2 aass)

insertb :: BExpr -> Assignments -> (BExpr, Assignments)
insertb (BoolConst x) ys = (BoolConst x, ys)
insertb (Not x) ys = (\(s,t) -> (Not s,t)) (insertb x ys)
insertb (BBinary op expr1 expr2) ass = ((BBinary op aexpr bexpr), bass)
                                     where (aexpr, aass) = (insertb expr1 ass)
                                           (bexpr, bass) = (insertb expr2 aass)
insertb (RBinary op expr1 expr2) ass =((RBinary op aexpr bexpr), bass)
                                     where (aexpr, aass) = (insert expr1 ass)
                                           (bexpr, bass) = (insert expr2 aass)

replace :: Var -> (AExpr, Assignments) -> Assignments
replace s (t,ys)
         | null z = x : ys
         | otherwise = map (\v -> if s==fst v then x else v) ys
        where x = (s,t)
              z = filter (\u -> s==(fst u)) ys
