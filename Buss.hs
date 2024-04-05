module Buss
-- =====================
-- Draws proof trees in LaTeX using the bussproofs.sty package

-- =====================

-- Tree(Axiom Unary Binary Trinery)

-- lll treewidth treeProof latexenv latexenvl latexcmd1 latexmath latexsmall latexmathrm latexmathbf
-- mathmacro1 latexFormula latexFormulaB latexArgs latexTerm axiom unary binary trinary rlabel 
-- bussTree latexTree latexProof goalStackToContext latexPartialProof latexCurrentGoal  
-- latexContext latexCenter latexTabular latexdoc (++++)

-- set of functions latex*Symbol (* stands for the name of a rule)

-- latexAndIntrSymbol latexAndElilSymbol latexAndElirSymbol
-- latexOrIntrlSymbol latexOrIntrrSymbol latexOrElimSymbol 
-- latexImpElimSymbol latexImpIntrSymbol
-- latexExFQSymbol latexReAASymbol
-- latexAllIntrSymbol latexAllElimSymbol
-- latexExIntrSymbol latexExElimSymbol

  where

import Perhaps
import Parser
import Formula
import Proof


{-
                    A     B
                   --------- X
                       C

       use the commands  

              \AxiomC{A}
              \AxiomC{B}
              \RightLabel{X}
              \BinaryInfC{C}
              \DisplayProof

-}

data Tree = Axiom   (String,String) 
          | Unary   (String,String) Tree
          | Binary  (String,String) Tree Tree
          | Trinary (String,String) Tree Tree Tree



lll (l1,l2) = length l1 + length l2

treewidth :: Tree -> Int
treewidth (Axiom l) = lll l
treewidth (Unary l t) = max (lll l) (treewidth t)
treewidth (Binary l t1 t2) = max (lll l) (treewidth t1 + treewidth t2)
treewidth (Trinary l t1 t2 t3) = max (lll l) (sum (map treewidth [t1,t2,t3]))


treeProof :: Context -> Proof -> Tree
treeProof c p = 

   let f  = case endFormula c p of -- !
             {
              Success f -> f;
              Failure s -> error s
             }
       lf = latexFormula f
   in case p of
       {
        AnProof u         -> let v = if fst (last c) == u &&
                                         head u == '?'
                                      then latexmathbf u
                                      else u
                              in Axiom  (v ++ " : " ++ lf,"");
        AndIntr p1 p2     -> Binary  (lf,latexAndIntrSymbol) 
                                     (treeProof c p1) (treeProof c p2);
        AndElil p1        -> Unary   (lf,latexAndElilSymbol) (treeProof c p1);
        AndElir p1        -> Unary   (lf,latexAndElirSymbol) (treeProof c p1);
        OrIntrl p1 _      -> Unary   (lf,latexOrIntrlSymbol) (treeProof c p1);
        OrIntrr p1 _      -> Unary   (lf,latexOrIntrrSymbol) (treeProof c p1);
        OrElim p1 p2 p3   -> Trinary (lf,latexOrElimSymbol)  
                                     (treeProof c p1) (treeProof c p2) (treeProof c p3);
        ImpIntr p1 (u,f') -> Unary   (lf,latexImpIntrSymbol u f') 
                                     (treeProof ((u,f'):c) p1); 
        ImpElim p1 p2     -> Binary  (lf,latexImpElimSymbol)  
                                     (treeProof c p1) (treeProof c p2); 
        ExFQ p1 _         -> Unary   (lf,latexExFQSymbol)      (treeProof c p1);
        ReAA p1           -> Unary   (lf,latexReAASymbol)      (treeProof c p1);
        AllIntr p1 s      -> Unary   (lf,latexAllIntrSymbol)   (treeProof c p1);
        AllElim p1 t      -> Unary   (lf,latexAllElimSymbol)   (treeProof c p1);
        Override p1 t     -> Unary   (lf,latexAllElimSymbol)   (treeProof c p1);
        ExIntr p1 s f t   -> Unary   (lf,latexExIntrSymbol)    (treeProof c p1);
        ExElim p1 p2      -> Binary  (lf,latexExElimSymbol)
                                     (treeProof c p1)  (treeProof c p2)
       }
        
latexenv :: String -> String -> String
latexenv name arg = "{\\" ++ name ++ " " ++ arg ++ "}"

latexenvnl :: String -> String -> String
latexenvnl name arg = 
  if name == "normal" then arg else "{\\" ++ name ++ "\n" ++ arg ++ "\n}"

latexcmd1 :: String -> String -> String
latexcmd1 name arg = "\\" ++ name ++ "{" ++ arg ++ "}"

latexmath :: String -> String
latexmath str = "$" ++ str ++ "$"

latexsmall :: String -> String
latexsmall = latexenv "small"

latexmathrm :: String -> String
latexmathrm = latexcmd1 "mathrm"

latexmathbf :: String -> String
latexmathbf = latexcmd1 "mathbf"

mathmacro1 :: String -> String -> String
mathmacro1 name = latexcmd1 name . latexmath

latexAndIntrSymbol, latexAndElilSymbol, latexAndElirSymbol :: String
latexAndIntrSymbol = "\\land^+" 
latexAndElilSymbol = "\\land^-" ++ latexmathrm "l" 
latexAndElirSymbol = "\\land^-" ++ latexmathrm "r"

latexOrIntrlSymbol, latexOrIntrrSymbol, latexOrElimSymbol :: String
latexOrIntrlSymbol = "\\lor^+" ++ latexmathrm "l"
latexOrIntrrSymbol = "\\lor^+" ++ latexmathrm "r"
latexOrElimSymbol  = "\\lor^-" 

latexImpIntrSymbol :: AnVar -> Formula -> String
latexImpIntrSymbol u f = "\\to^+\\," ++ u ++ " : " ++ latexFormula f

latexImpElimSymbol, latexExFQSymbol, latexReAASymbol :: String
latexImpElimSymbol = "\\to^-"
latexExFQSymbol     = latexmathrm "efq"
latexReAASymbol     = latexmathrm "raa"

latexAllIntrSymbol, latexAllElimSymbol :: String
latexAllIntrSymbol = "\\forall^+"
latexAllElimSymbol = "\\forall^-"

latexExIntrSymbol, latexExElimSymbol :: String
latexExIntrSymbol = "\\exists^+"
latexExElimSymbol = "\\exists^-"

latexFormula :: Formula -> String
latexFormula f = case f of
  {
   Atom str []  -> str;
   Atom str l   -> str ++ "(" ++ latexArgs l ++ ")";
   And f1 f2    -> latexFormulaB f1 ++ "\\land " ++ latexFormulaB f2;
   Or  f1 f2    -> latexFormulaB f1 ++ "\\lor "  ++ latexFormulaB f2;
   Imp f1 f2    -> latexFormulaB f1 ++ "\\to "   ++ latexFormulaB f2;
   Bot          -> "\\bot";
   All x g      -> "\\forall " ++ x ++ "\\; " ++ latexFormulaB g;
   Ex x g       -> "\\exists " ++ x ++ "\\; " ++ latexFormulaB g
  }
  
latexFormulaB :: Formula -> String
latexFormulaB f = case f of
  {
   Atom _ _     -> latexFormula f;
   Bot          -> latexFormula f;
   All _ _      -> latexFormula f;
   Ex _ _       -> latexFormula f; 
   _            -> "(" ++ latexFormula f ++ ")"
  }
  
latexArgs :: [Term] -> String
latexArgs [] = ""
latexArgs [x] = latexTerm x
latexArgs (x:xs) = latexTerm x ++ ", " ++ latexArgs xs

latexTerm :: Term -> String
latexTerm (Var x) = x
latexTerm (Const c) = latexmathrm c --  "\\mathrm{" ++ c ++ "}"
latexTerm (Fun fun ts) = latexmathrm fun ++ "(" ++ latexArgs ts ++ ") "
                      -- fun ++ "(" ++ latexArgs ts ++ ") "


axiom,unary,binary,trinary,rlabel :: String -> String
axiom   = mathmacro1 "AxiomC"
unary   = mathmacro1 "UnaryInfC"
binary  = mathmacro1 "BinaryInfC"
trinary = mathmacro1 "TrinaryInfC"
rlabel  = mathmacro1 "RightLabel" 

bussTree :: Tree -> [String]
bussTree t = aux t ["\\DisplayProof"]  where

  aux :: Tree -> [String] -> [String]
  aux t cont = case t of
   {
    Axiom   (s,l)          -> rlabel l : axiom s : cont;
    Unary   (s,l) t1       -> aux t1 (rlabel l : unary s : cont);
    Binary  (s,l) t1 t2    -> (aux t1 . aux t2) (rlabel l : binary s : cont);
    Trinary (s,l) t1 t2 t3 -> (aux t1 . aux t2 . aux t3) (rlabel l : trinary s : cont)
   }

latexTree :: Tree -> String
latexTree = unlines . bussTree 

{-
latexProof :: Context -> Proof -> String
latexProof c p = latexTree (treeProof c p)
-}


latexProof :: Context -> Proof -> String
latexProof c p = let {
                       t = treeProof c p;
                       w = treewidth t;
                       size = if w < 50 then "large" else
                              if w < 100 then "normal" else
                              if w < 150 then "small"  else
                              if w < 200 then "footnotesize" else "tiny"
                     }
                  in latexenvnl size (latexTree t)



{-
type Label   = String
type Context = [Assumpt]
type Assumpt = (Label, Formula)
type Goal    = (Assumpt, Context)
type GlStack = [Goal]
type AnVar = Label
type GlSymbol = Label
 
type PlProof = (GlStack, Context, Proof)
-}


goalStackToContext :: GlStack -> Context
goalStackToContext = reverse . map fst

latexPartialProof :: PlProof -> String
latexPartialProof (gs,c,p) = 
  latexProof (c ++ goalStackToContext gs) p ++
  (if null gs
   then ""
   else latexCurrentGoal (head gs)) 
 
latexCurrentGoal :: Goal -> String
latexCurrentGoal ((u,f),c) = 
  "\n\\bigskip\n\n Current goal:\\quad" ++
  "$" ++ latexmathbf u ++ " : " ++ latexFormula f ++ "$\n\\medskip\n\n" ++
  (if null c then "" else "Assumptions available:" ++ latexContext c)

latexContext :: Context -> String
latexContext c =
   (latexTabular "ll") 
     [[latexmath u++"\\ :",latexmath(latexFormula f)] | (u,f) <- c] 

latexCenter :: String -> String
latexCenter s = "\\begin{center}" ++ s ++ "\\end{center}"

latexTabular :: String -> [[String]] -> String
latexTabular alignment ls =
      "\\begin{tabular}{" ++ alignment ++ "}\n" ++
      unlines (map latexline ls) ++
      "\\end{tabular}\n"
 where
    latexline :: [String] -> String  
    latexline (s0:s1:rest) = s0 ++ "&" ++ latexline (s1:rest)
    latexline [s]          = s ++ "\\\\\n"
    latexline []           = "\\\\\n"

{-
latexdoc :: String -> String
latexdoc str = unlines ["\\documentclass{article}",
                        "\\usepackage{bussproofs}",
                        "\\pagestyle{empty}",
                        "\\parindent=0mm",
                        "\\begin{document}",
                        str,
                        "\\end{document}"]
-}

latexdoc :: String -> String
latexdoc str = unlines ["\\documentclass{article}",
                        "\\advance\\oddsidemargin by -1in",
                        "\\advance\\textwidth by 2in",
                        "\\advance\\topmargin by -1in",
                        "\\advance\\textheight by 2.0in",
                        "\\usepackage[margin=1cm,portrait,a4paper]{geometry}", -- do not commit
                        "\\usepackage{bussproofs}",
--                        "\\usepackage[hypertex]{hyperref}",
                        "\\pagestyle{empty}",
                        "\\parindent=0mm",
                        "\\begin{document}",
                        str,
                        "\\end{document}"]




(++++) :: String -> String -> String
s ++++ t = s ++ "\n\\bigskip\n\n" ++ t

{-
\advance\oddsidemargin by -1in
\advance\textwidth by 2in
\advance\topmargin by -1in
\advance\textheight by 2.0in
-}
