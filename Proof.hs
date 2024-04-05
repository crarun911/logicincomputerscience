module Proof
-- ==================================
-- Defines data type of a proof, refines and replaces proofs 
-- and generates an end formula based on the context and a proof, 
-- performs appropriate correctness checks

-- ==================================

-- AnVar Assumpt Context GlStack GlSymbol Goal Label PlProof
-- Command(AssumptBW AndIntrBW AndElilBW AndElirBW ImpIntrBW ImpElimBW OrIntrlBW 
--         OrIntrrBW OrElimBW ExFQBW ReAABW AllIntr AllElim ExIntr ExElim Invalid)
-- Proof(AnProof AndIntr AndElim ExFQ ImpIntr ImpElim OrIntrl OrIntrr 
--       OrElim ReAA AllIntr AllElim ExIntr ExElim) 

-- assumpt_label assumpt_formula goal_assumpt goal_ctx
-- currentGoal goalstrack checkVarCondition fvInContext endFormula replace refine start 

-- A set of functions refine*BW 
-- refineAssumptBW, refineAndIntrBW, refineAndElilBW, refineAndElirBW, 
-- refineImpIntrBW, refineImpElimBW, refineOrIntrlBW, refineOrIntrrBW, refineOrElimBW, 
-- refineExFQBW, refineReAABW, 
-- refineAllIntrBW, refineAllElimBW, refineExIntrBW, refineExElimBW

-- A set of functions endF* 
-- endFAndIntr, endFAndElil, endFAndElir, 
-- endFImpIntr, endFImpElim, endFOrIntrl, endFOrIntrr, endFOrElim, 
-- endFExFQ, endFReAA, 
-- endFAllIntr, endFAllElim,  endFExIntr, endFExElim


  where

import Parser
import Formula 
import Perhaps

import Data.List as L

{- 
Gamma, u: A |- g2: B
-----------------------
      Gamma |- g1: A -> B
      
"Gamma" is Context
"u: A" is Assumpt (u, A)
"u" is Label
"A", "B", "A -> B" is Formula
"g1", "g2" is GlSymbol
-}

type Label   = String
type Context = [Assumpt]
type Assumpt = (Label, Formula)
type Goal    = (Assumpt, Context)
type GlStack = [Goal]
type AnVar = Label
type GlSymbol = Label

assumpt_label :: Assumpt -> Label
assumpt_label = fst

assumpt_formula :: Assumpt -> Formula
assumpt_formula = snd

goal_assumpt :: Goal -> Assumpt
goal_assumpt = fst

goal_ctx :: Goal -> Context
goal_ctx = snd

data Proof = AnProof Label -- 
             | AndIntr Proof Proof
             | AndElil Proof
             | AndElir Proof
             | ImpIntr Proof Assumpt
             | ImpElim Proof Proof
             | OrIntrl Proof Formula
             | OrIntrr Proof Formula
             | OrElim Proof Proof Proof
             | ExFQ Proof Formula
             | ReAA Proof
             | AllIntr Proof String              -- String is a variable, e.g. x
             | AllElim Proof Term
             | ExIntr Proof String Formula Term  -- ExIntr (p:A(t)) x A(x) t
             | ExElim Proof Proof      -- ExElim (p: ex x A(x))  (q: All y (A(y) -> C)) x not in C
             | Override Proof Formula  -- for display of allElim; endFormula (Override p f) = f
           deriving (Show, Eq, Read)

type PlProof = (GlStack, Context, Proof)

currentGoal :: PlProof -> Perhaps Goal
currentGoal (gs,_,_) = if null gs 
                       then Failure "No goal" 
                       else Success (head gs)

goalstack :: PlProof -> GlStack
goalstack (gs,_,_) = gs

checkVarCondition v ctx =
  not $ any (free v) (map snd $ filter (\(l, _) -> head l /= '?') ctx)

fvInContext :: Context -> [String]
fvInContext ctx =
  let {
       ctx' = filter (\(l, _) -> head l /= '?') ctx
      }
  in unions (map (fv.snd) ctx')
  
data Command = AssumptBW AnVar -- use rule/placeholder
               | AndIntrBW GlSymbol GlSymbol
               | AndElilBW GlSymbol Formula
               | AndElirBW GlSymbol Formula
               | ImpIntrBW GlSymbol AnVar
               | ImpElimBW GlSymbol GlSymbol Formula
               | OrIntrlBW GlSymbol
               | OrIntrrBW GlSymbol
               | OrElimBW GlSymbol GlSymbol GlSymbol Formula
               | ExFQBW GlSymbol
               | ReAABW GlSymbol
               | AllIntrBW GlSymbol -- AllIntrBW ? from goal All x.P(x) obtain? P(x)
               | AllElimBW GlSymbol Formula Term -- AllElimBW ? x P(x) t from goal P(t) obtain ? All x.P(x)
               | AllElimBWX GlSymbol Formula 
               | ExIntrBW GlSymbol Term -- ExIntrBW ? t from goal Ex x.P(x) obtain ? P(t)
               | ExElimBW GlSymbol GlSymbol Formula 
                 -- ExElimBW ?1 ?2 x P(x)  from goal C obtain goals ?1 Ex x.P(x) ?2 All x.(P(x) -> C)
               | Invalid 
             deriving (Show, Eq, Read)

endFormula :: Context -> Proof -> Perhaps Formula
endFormula ctx p = 
  case p of
   {
    AnProof av -> look av ctx;
    AndIntr p1 p2 -> endFAndIntr ctx p1 p2;
    AndElil p1 -> endFAndElil ctx p1;
    AndElir p1 -> endFAndElir ctx p1;
    ImpIntr p1 avf -> endFImpIntr ctx p1 avf;
    ImpElim p1 p2 -> endFImpElim ctx p1 p2;
    OrIntrl p1 f -> endFOrIntrl ctx p1 f;
    OrIntrr p1 f -> endFOrIntrr ctx p1 f;
    OrElim p1 p2 p3 -> endFOrElim ctx p1 p2 p3;
    ExFQ p1 f -> endFExFQ ctx p1 f;
    ReAA p1 -> endFReAA ctx p1;
    AllIntr p1 x -> endFAllIntr ctx p1 x;
    AllElim p1 t -> endFAllElim ctx p1 t;
    ExIntr p1 x f t -> endFExIntr ctx p1 x f t;
    ExElim p1 p2 -> endFExElim ctx p1 p2;
    Override p1 f -> return f
   }
                 
replace :: Proof -> Label -> Proof -> Proof
replace p u q = 
  case p of
   {
    AnProof av -> if av == u then q else p;
    AndIntr p1 p2 -> AndIntr (replace p1 u q) (replace p2 u q);
    AndElil p1 -> AndElil (replace p1 u q);
    AndElir p1 -> AndElir (replace p1 u q);
    ImpIntr p1 avf -> ImpIntr (replace p1 u q) avf;
    ImpElim p1 p2 -> ImpElim (replace p1 u q) (replace p2 u q);
    OrIntrl p1 f -> OrIntrl (replace p1 u q) f;
    OrIntrr p1 f -> OrIntrr (replace p1 u q) f;
    OrElim p1 p2 p3 -> OrElim (replace p1 u q) (replace p2 u q) (replace p3 u q);
    ExFQ p1 f -> ExFQ (replace p1 u q) f;
    ReAA p1 -> ReAA (replace p1 u q);
    AllIntr p1 x -> AllIntr (replace p1 u q) x;
    AllElim p1 t -> AllElim (replace p1 u q) t;
    ExIntr p1 x f t -> ExIntr (replace p1 u q) x f t;
    ExElim p1 p2 -> ExElim (replace p1 u q) (replace p2 u q);
    Override p1 f -> Override (replace p1 u q) f
   }
   
--downtoup
refine :: PlProof -> Command -> Perhaps PlProof
refine pp@((a0,c0):gs,ctx,p) cmd = 
  case cmd of
   {
    AssumptBW av -> refineAssumptBW pp av;
    AndIntrBW gl1 gl2 -> refineAndIntrBW pp gl1 gl2;
    AndElilBW gl f -> refineAndElilBW pp gl f;
    AndElirBW gl f -> refineAndElirBW pp gl f;
    ImpIntrBW gl av -> refineImpIntrBW pp gl av;
    ImpElimBW gl1 gl2 f -> refineImpElimBW pp gl1 gl2 f;
    OrIntrlBW gl -> refineOrIntrlBW pp gl;
    OrIntrrBW gl -> refineOrIntrrBW pp gl;
    OrElimBW gl1 gl2 gl3 f -> refineOrElimBW pp gl1 gl2 gl3 f;
    ExFQBW gl -> refineExFQBW pp gl;
    ReAABW gl -> refineReAABW pp gl;                                
    AllIntrBW gl -> refineAllIntrBW pp gl;
    AllElimBW gl f t -> refineAllElimBW pp gl f t;
    -- BWX is only used for displaying a hint to the user  
    AllElimBWX gl f -> refineAllElimBWX pp gl f;                                          
    ExIntrBW gl t -> refineExIntrBW pp gl t;
    ExElimBW gl1 gl2 f -> refineExElimBW pp gl1 gl2 f;                                         
    Invalid -> fail ("invalid command: " ++ show cmd)
   }                   

start :: Label -> Formula -> PlProof
start g f = ([((g,f),[])],[],AnProof g) 



-- refine sub-functions
refineAssumptBW :: PlProof -> AnVar -> Perhaps PlProof
refineAssumptBW ((a0,c0):gs,ctx,p) av =
  do {
      f1 <- look av (c0 ++ ctx);
      if compareF f1 (assumpt_formula a0)
      then let p1 = replace p (assumpt_label a0) (AnProof av)
        in return (gs,ctx,p1)
      else fail ("assumption doesn't fit: " ++ show av)
     }
     
refineAndIntrBW :: PlProof -> GlSymbol -> GlSymbol -> Perhaps PlProof
refineAndIntrBW ((a0,c0):gs,ctx,p) gl1 gl2 =
  case (assumpt_formula a0) of
   {
    And f1 f2 ->
      let {
           g1 = ((gl1,f1),c0);
           g2 = ((gl2,f2),c0);
           p1 = replace p (assumpt_label a0)
                 (AndIntr (AnProof gl1) (AnProof gl2))
          }
      in return (g1:g2:gs,ctx,p1);
    _ -> fail ("AndIntrBW, wrong command: " ++ show a0)
   }  

refineAndElilBW :: PlProof -> GlSymbol -> Formula -> Perhaps PlProof
refineAndElilBW ((a0,c0):gs,ctx,p) gl f =
  let {
       f1 = And (assumpt_formula a0) f;
       g1 = ((gl,f1),c0);
       p1 = replace p (assumpt_label a0) (AndElil (AnProof gl))
      }
  in return (g1:gs,ctx,p1)
  
refineAndElirBW :: PlProof -> GlSymbol -> Formula -> Perhaps PlProof
refineAndElirBW ((a0,c0):gs,ctx,p) gl f =
  let {
       f1 = And f (assumpt_formula a0);
       g1 = ((gl,f1),c0);
       p1 = replace p (assumpt_label a0) (AndElir (AnProof gl))
      }
  in return (g1:gs,ctx,p1)
  
refineImpIntrBW :: PlProof -> GlSymbol -> AnVar -> Perhaps PlProof
refineImpIntrBW ((a0,c0):gs,ctx,p) gl av =
  case (assumpt_formula a0) of
   {
    Imp f1 f2 ->
      let {
           a = (gl,f2);
           c = (av,f1):c0;
           p1 = replace p (assumpt_label a0) (ImpIntr (AnProof gl) (av, f1))
          }
      in return ((a,c):gs,ctx,p1);
      _ -> fail ("ImpIntrBW, wrong command: " ++ show a0)
     }

refineImpElimBW :: PlProof -> GlSymbol -> GlSymbol -> Formula -> Perhaps PlProof
refineImpElimBW ((a0,c0):gs,ctx,p) gl1 gl2 f =
  let {
       f1 = Imp f (assumpt_formula a0);
       g1 = ((gl1,f1),c0);
       g2 = ((gl2,f),c0);
       p1 = replace p (assumpt_label a0) (ImpElim (AnProof gl1) (AnProof gl2))
      }
  in return (g1:g2:gs,ctx,p1)
  
refineOrIntrlBW :: PlProof -> GlSymbol -> Perhaps PlProof
refineOrIntrlBW ((a0,c0):gs,ctx,p) gl =
  case (assumpt_formula a0) of
   {
    Or f1 f2 ->
      let {
           g1 = ((gl,f1),c0);
           p1 = replace p (assumpt_label a0) (OrIntrl (AnProof gl) f2)
          }
      in return (g1:gs,ctx,p1);
    _ -> fail ("OrIntrlBW, wrong command: " ++ show a0)
   }
   
refineOrIntrrBW :: PlProof -> GlSymbol -> Perhaps PlProof
refineOrIntrrBW ((a0,c0):gs,ctx,p) gl =
  case (assumpt_formula a0) of
   {
    Or f1 f2 ->
      let {
           g1 = ((gl,f2),c0);
           p1 = replace p (assumpt_label a0) (OrIntrr (AnProof gl) f1)
          }
      in return (g1:gs,ctx,p1);
    _ -> fail ("OrIntrrBW, wrong command: " ++ show a0)
   }
   
refineOrElimBW :: PlProof -> GlSymbol -> GlSymbol -> GlSymbol -> Formula -> Perhaps PlProof
refineOrElimBW ((a0,c0):gs,ctx,p) gl1 gl2 gl3 f =
  case f of
   {
    Or f1 f2 ->
      let {
           f3 = Imp f1 (assumpt_formula a0);
           f4 = Imp f2 (assumpt_formula a0);
           g1 = ((gl1,f),c0);
           g2 = ((gl2,f3),c0);
           g3 = ((gl3,f4),c0);
           p1 = replace p (assumpt_label a0) (OrElim (AnProof gl1) (AnProof gl2) (AnProof gl3))
          }
      in return (g1:g2:g3:gs,ctx,p1);
    _ -> fail ("OrElimBW, wrong command: " ++ show a0)
   }

refineExFQBW :: PlProof -> GlSymbol -> Perhaps PlProof
refineExFQBW ((a0,c0):gs,ctx,p) gl =
  let {
       f1 = Bot;
       g1 = ((gl,f1),c0);
       p1 = replace p (assumpt_label a0) (ExFQ (AnProof gl) (assumpt_formula a0))
      }
  in return (g1:gs,ctx,p1)
  
refineReAABW :: PlProof -> GlSymbol -> Perhaps PlProof
refineReAABW ((a0,c0):gs,ctx,p) gl =
  let {
       f1 = Imp (Imp (assumpt_formula a0) Bot) Bot;
       g1 = ((gl,f1),c0);
       p1 = replace p (assumpt_label a0) (ReAA (AnProof gl))
      }
  in return (g1:gs,ctx,p1)
  
refineAllIntrBW :: PlProof -> GlSymbol -> Perhaps PlProof
refineAllIntrBW ((a0,c0):gs,ctx,p) gl =
  case (assumpt_formula a0) of
   {
    All v f ->
      let {
           v' = freshVar v (Formula.union (fvInContext c0) (fv (All v f)));
           f' = substituteFormula v (Var v') f;
           g1 = ((gl,f'), c0);
           p1 = replace p (assumpt_label a0) (AllIntr (AnProof gl) v')
          }
        in return (g1:gs,ctx,p1);
    _ -> fail ("AllIntrBW, wrong command: " ++ show a0)
   }
   
refineAllElimBW :: PlProof -> GlSymbol -> Formula -> Term -> Perhaps PlProof
refineAllElimBW ((a0,c0):gs,ctx,p) gl f t = 
  case f of
   {
    All v f0 ->
      let f1 = substituteFormula v t f0 in
      if (compareF f1 (assumpt_formula a0)) then
        let {
             g1 = ((gl, f), c0);
             p1 = replace p (assumpt_label a0) (AllElim (AnProof gl) t)
            }
        in return (g1:gs,ctx,p1)
      else fail ("AllElimBW, formulas don't fit: " ++ show a0 ++ " " ++ show f1);
    _ -> fail ("AllElimBW, universal formula expected")
   }

refineAllElimBWX :: PlProof -> GlSymbol -> Formula -> Perhaps PlProof
refineAllElimBWX ((a0,c0):gs,ctx,p) gl f = 
  case f of 
   {
    All v f0 ->
      let {
           g1 = ((gl, f), c0);
           p1 = replace p (assumpt_label a0) (Override (AnProof gl) (assumpt_formula a0))
          }
      in return (g1:gs,ctx,p1);                          
    _ -> fail ("AllElimBW, universal formula expected")
   }
   
refineExIntrBW :: PlProof -> GlSymbol -> Term -> Perhaps PlProof
refineExIntrBW ((a0,c0):gs,ctx,p) gl t = 
  case (assumpt_formula a0) of
   {
    Ex v f ->
      let {
           f1 = substituteFormula v t f;
           g1 = ((gl,f1), c0);
           p1 = replace p (assumpt_label a0) (ExIntr (AnProof gl) v f t)
          }
      in return (g1:gs,ctx,p1);
    _ -> fail ("ExIntrBW, command not applicable to: " ++ showFormula (assumpt_formula a0))
   }
   
refineExElimBW :: PlProof -> GlSymbol -> GlSymbol -> Formula -> Perhaps PlProof
refineExElimBW ((a0,c0):gs,ctx,p) gl1 gl2 f =
  case f of
   {
    Ex v f0 ->
      if not (free v (assumpt_formula a0)) then 
        let {
             f2 = All v (Imp f0 (assumpt_formula a0));
             g1 = ((gl1, f), c0);
             g2 = ((gl2, f2), c0);
             p1 = replace p (assumpt_label a0) (ExElim (AnProof gl1) (AnProof gl2));
            }
        in return (g1:g2:gs,ctx,p1)
      else fail ("ExElimBW, provided variable: " ++ v ++ " must not be free in the current goal.");
    _ -> fail ("ExElimBW, existential formula expected")
   }
   
-- endFormula sub-functions
endFAndIntr :: Context -> Proof -> Proof -> Perhaps Formula
endFAndIntr ctx p1 p2 =
  do {
      f1 <- endFormula ctx p1;
      f2 <- endFormula ctx p2;
      return (And f1 f2)
     }

endFAndElil :: Context -> Proof -> Perhaps Formula 
endFAndElil ctx p1 =
  do {
      f <- endFormula ctx p1;
      case f of
       {
        And f1 f2 -> return f1;
        _ -> fail ("AndElil, formula doesn't fit: " ++ show f)
       }
      }
      
endFAndElir :: Context -> Proof -> Perhaps Formula 
endFAndElir ctx p1 =
  do {
      f <- endFormula ctx p1;
      case f of
       {
        And f1 f2 -> return f2;
        _ -> fail ("AndElir, formula doesn't fit: " ++ show f)
       }
      }
      
endFImpIntr :: Context -> Proof -> Assumpt -> Perhaps Formula
endFImpIntr ctx p1 avf =
  do {
      f <- endFormula (avf:ctx) p1;
      return (Imp (snd avf) f)
     }
     
endFImpElim :: Context -> Proof -> Proof -> Perhaps Formula
endFImpElim ctx p1 p2 =
  do {
      f1 <- endFormula ctx p1;
      f2 <- endFormula ctx p2;
      case f1 of
       {
        Imp f11 f12 ->
          if compareF f11 f2
          then return f12
          else fail ("ImpElim, formulae don't fit: " ++ show f1 ++ ", " ++ show f2);
        _ -> fail ("ImpElim, formula doesn't fit: " ++ show f1)
       }
      }

endFOrIntrl :: Context -> Proof -> Formula -> Perhaps Formula
endFOrIntrl ctx p1 f =
  do {
      f1 <- endFormula ctx p1;
      return (Or f1 f)
     }
     
endFOrIntrr :: Context -> Proof -> Formula -> Perhaps Formula
endFOrIntrr ctx p1 f =
  do {
      f1 <- endFormula ctx p1;
      return (Or f f1)
     }

endFOrElim :: Context -> Proof -> Proof -> Proof -> Perhaps Formula
endFOrElim ctx p1 p2 p3 =
  do {
      f1 <- endFormula ctx p1;
      f2 <- endFormula ctx p2;
      f3 <- endFormula ctx p3;
      case (f1,f2,f3) of
       {
        (Or f11 f12, Imp f21 f22, Imp f31 f32) ->
          if (compareF f11 f21)&&(compareF f12 f31)&&(compareF f22 f32)
          then return f32
          else fail ("OrElim, formulae don't fit " ++ show f1 ++ ", "++ show f2 ++ ", " ++ show f3);
        _ -> fail ("OrElim, formulae don't fit " ++ show f1 ++ ", "++ show f2 ++ ", " ++ show f3)
       }
      }
      
endFExFQ :: Context -> Proof -> Formula -> Perhaps Formula
endFExFQ ctx p1 f =
  do {
      f1 <- endFormula ctx p1;
      case f1 of
       {
        Bot -> return f;
        _   -> fail ("ExFQ, formula doesn't fit: "++ show f1)
       }
      }
      
endFReAA :: Context -> Proof -> Perhaps Formula
endFReAA ctx p1 =
  do {
      f <- endFormula ctx p1;
      case f of
       {
        Imp (Imp f Bot) Bot -> return f;
        _  -> fail ("ReAA, formula doesn't fit: "++ show f)
       }
      }
      
endFAllIntr :: Context -> Proof -> String -> Perhaps Formula
endFAllIntr ctx p1 x =
  do { -- x must not occur free in any free assumption valid at this point!
      f <- endFormula ctx p1;
      -- ! quick fix to ignore elements from the goal stack added to the end of the list
      -- because latexFormula adds goals to the context
      if not (checkVarCondition x ctx)
      then fail ("AllIntr, variable condition violated: " ++ showFormula f)
      else return (All x f)
     }

endFAllElim :: Context -> Proof -> Term -> Perhaps Formula
endFAllElim ctx p1 t =
 do {
     f <- endFormula ctx p1;
     case f of
      {
       All x g -> return (substituteFormula x t g);
       _ -> fail ("AllElim, formula doesn't fit: " ++ show f)
      }
     }
     
endFExIntr :: Context -> Proof -> String -> Formula -> Term -> Perhaps Formula
endFExIntr ctx p1 x f t =
  do {
      f1 <- endFormula ctx p1;
      let f' = substituteFormula x t f in
      if compareF f' f1 
      then return (Ex x f)
      else fail ("ExInr, formula doesn't fit: " ++ show f1)
     }
     
endFExElim :: Context -> Proof -> Proof -> Perhaps Formula
endFExElim ctx p1 p2 =
  do { -- ExElim (p: ex x A(x))  (q: All y (A(y) -> C))  x not in C
       -- x must not occur free in C!
      f1 <- endFormula ctx p1;
      f2 <- endFormula ctx p2;
      case (f1, f2) of 
       {
        (Ex x fa, All y (Imp fa' fc)) -> 
          if compareF (All x fa) (All y fa') && not (free y fc) 
          then return fc
          else fail ("Formulas don't match: " ++ showFormula f1 ++ " " ++ showFormula f2 ++ " or "
                     ++ x ++ " is not free in " ++ showFormula fc);
        _ -> fail ("ExElim, formulas don't fit: " ++ showFormula f1 ++ " " ++ showFormula f2)
       }
      }

{-
-- AllElimBW test1
--allel1_state0 = start "a0" (runP0 parseFormula "P(t)")
allel1_state1 = refine allel1_state0 (AllElimBW "a1" "x" (Atom "P" [Var "x"]) (Const "t"))
allel1_state1' = Success ([(("a1", All "x" (Atom "P" [Var "x"])),[])],[],AllElim (AnProof "a1") (Const "t"))

-- ExIntrBW test1
exin1_state0 = start "a0" (runP0 parseFormula "ex x P(x)")
exin1_state1 = refine exin1_state0 (ExIntrBW "a1" (Const "t"))
exin1_state1' = Success ([(("a1",Atom "P" [Const "t"]),[])],[],ExIntr (AnProof "a1") "x" (Atom "P" [Var "x"]) (Const "t"))

exel1_state0 = start "a0" (runP0 parseFormula "B(x)")
exel1_state1 = refine exel1_state0 (ExElimBW "a1" "a2" "y" (runP0 parseFormula "P(y)"))
exel1_state1' = Success ([(("a1",Atom "P" [Const "t"]),[])],[],ExIntr (AnProof "a1") "x" (Atom "P" [Var "x"]) (Const "t"))

test_state0 = start "a0" (pF "(all x P(x)) -> (ex y P(y))")
test_state1 = refine test_state0 (ImpIntrBW "expy" "allpx")
test_state2 = test_state1 >>= \s -> refine s (ExIntrBW "pt" (Var "t"))
test_state3 = test_state2 >>= \s -> refine s (AllElimBW "allpy" "z" (pF "P(z)") (Var "t"))
test_state4 = test_state3 >>= \s -> refine s (AssumptBW "allpx")
-}

-- for testinf: some incorrect proofs

pF = runP0 parseFormula

ip1,ip2 :: Proof
ip1 = ImpIntr (AnProof "w") ("v", Atom "A" [])
ip2 = ImpIntr (AndElir (AnProof "u")) ("u", Or (Atom "A" []) (Atom "B" []))

case_endFormula_ExIntr1 = 
  endFormula [("w", Atom "P" [Const "t"])] $ ExIntr (AnProof "w") "x" (Atom "P" [Var "x"]) (Const "t")
case_endFormula_ExElim1 = 
  endFormula [("u", Ex "x" (Atom "P" [Var "x"])), ("w", All "y" (Imp (Atom "P" [Var "y"]) (Atom "C" [])))] $ ExElim (AnProof "u") (AnProof "w")
