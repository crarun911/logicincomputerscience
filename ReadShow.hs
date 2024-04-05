module ReadShow
-- ========================
-- Interprets user input strings - parsing and pretty-printing 
-- for user interaction - and displays error messages and hints

-- ========================
-- ruleNames str2Input str2Inputs showState 
-- helptext fullhelp focusedhelp quithelp 
-- submithelp deletehelp sizehelp newhelp manualhelp
-- showGoal showContext showAssumpt showAssi showPP showError 
-- welcometextLong commandtextLong

  where

import Perhaps
import Parser
import Formula
import Proof
import Buss
import Step

terminalflag :: Bool
terminalflag = True
--  terminalflag = False


ruleNames :: [String]
ruleNames = ["use",   -- must be prefix free 
             "andi", "andel", "ander", 
             "impi", "impe", 
             "oril", "orir", "ore", 
             "efq", "raa", "alli", "alle", "falle",
             "exi", "exe"]

str2Input :: String -> Input
str2Input s =
  case s of
   {
    "use"    -> RuleI AssuR;
    "andi"   -> RuleI AndiR;
    "andel"  -> RuleI AndelR;
    "ander"  -> RuleI AnderR;
    "impi"   -> RuleI ImpiR;
    "impe"   -> RuleI ImpeR;
    "oril"   -> RuleI OrilR;
    "orir"   -> RuleI OrirR;
    "ore"    -> RuleI OreR;
    "efq"    -> RuleI EfqR;
    "raa"    -> RuleI RaaR;
    "alli"   -> RuleI AlliR;
    "alle"   -> RuleI AlleR;
    "falle"  -> RuleI AlleRF;
    "exi"    -> RuleI ExiR;
    "exe"    -> RuleI ExeR;
    _        -> TextI s
   }


 
str2Inputs :: String -> [Input]
str2Inputs s = 
  case runP (parseStrings ruleNames) s of
    ((ruleName,rest):_) -> str2Input ruleName :  
                             (if spacesOnly rest then [] else [TextI rest])
    []                  -> [TextI s]

-- helper functions for showing state
showGlFormula :: Perhaps Goal -> String
showGlFormula (Success g) = showFormula (snd (fst g))
-- showGlFormula (Success g) = showFormula' (snd (fst g))  --wrong!!!
showGlFormula (Failure s) = s

showAvAssumpt :: Perhaps Goal -> String
showAvAssumpt (Success g) = let {ctx = snd g} 
                            in if ctx == [] then "" else "Available assumptions" ++ showContext (snd g)
showAvAssumpt (Failure s) = ""

showGoalTerminal :: Bool -> PlProof -> String
showGoalTerminal b pp =
  if b
  then let {gl = currentGoal pp}
       in "\n --------------------------- \n" ++
          showAvAssumpt gl ++
          "Current goal: " ++ showGlFormula gl ++ "\n"
  else ""

showState :: State -> String
showState state@(out,ips,pp,xs,n) =
  case out of
  {
   ErrorO err -> showError err;
   StartO     -> "Enter goal formula X ";
{-
   OkO        ->  let {gl = currentGoal pp}
                  in "\n --------------------------- \n" ++
                     showAvAssumpt gl ++
                     "Current goal: " ++ showGlFormula gl ++ "\n" ++ 
-}
   OkO        ->  showGoalTerminal terminalflag pp ++  --
     case ips of
      {
       OkS       -> "Enter command";            
       StartS    -> "Enter goal formula";
       CompleteS -> 
          "Proof complete.\nEnter quit, submit <i>, delete <i>, new, or ?";
       UseS      -> "Enter assumption variable";
       ImpiS     -> "Enter assumption variable";
       ImpeS     -> "Enter missing formula X";
       AndelS    -> "Enter missing formula X";
       AnderS    -> "Enter missing formula X";
       OreS      -> "Enter missing formula of the form  X or Y";
       AlleS     -> "Enter the term you wish to generalise";
       AlleSF    -> "Enter the quantified formula of the form: all x A(x)";
       ExiS      -> "Enter a term that should substitute the variable";
       ExeS      -> "Enter missing formula of the form: ex x A(x)"
      };
   Unsound gas   -> "\n WARNING!\n\n" ++
                   "Your proof attempt cannot be completed because\n" ++
                   "the " ++
                   (if length gas == 1 
                    then "goal below is " 
                    else "goals below are ") ++
                   "invalid and therefore unprovable.\n"++
                   concat [ showGoal goal ++ "\nCounterexample:\n" 
                            ++ showAssi assi ++ "\n" | (goal,assi) <- gas ] ++
                   "\nConsider undo or quit.\n\n"
  }

helptext :: [String] -> String
helptext ws = case ws of { [] -> fullhelp ; (w:_) ->  focusedhelp w }

fullhelp :: String
fullhelp = quithelp ++ submithelp ++ deletehelp ++ sizehelp ++ newhelp ++ manualhelp

focusedhelp :: String -> String
focusedhelp w = case w of
                  {
                    "quit"   -> quithelp ;
                    "submit" -> submithelp ;
                    "delete" -> deletehelp ;
                    "size"   -> sizehelp ;
                    "new"    -> newhelp
                  }

quithelp, submithelp, deletehelp, sizehelp, newhelp, manualhelp :: String 

quithelp = "\n quit:\n end the prover program "++
           "(you will loose the proof if you didn't submit it).\n"

submithelp = "\n submit <i>:\n submit the proof you just completed" ++ 
             " as answer to Question <i>.\n" ++
 " Repeating the command (possibly with a new proof or with changed size)\n "++
 " will override the old proof.\n"

deletehelp = "\n delete <i>:\n delete Question <i>.\n" 

sizehelp = "\n size <i> <size>:\n display Question <i> in size <size>.\n"++
    " Possible values for <size> are: small, footnotesize, tiny, normal.\n"++
    " This command is useful if the proof is too big to fit on the page.\n"

newhelp =  "\n new:\n start a new proof.\n"   

manualhelp = "For more help see the USER-MANUAL in this directory"

showGoal :: Goal -> String
showGoal (assu,gamma) = showContext gamma ++ " |-\n" ++ showAssumpt assu

showContext :: Context -> String
showContext gamma = "\n" ++ concat (map showAssumpt gamma)

showAssumpt :: Assumpt -> String
showAssumpt (u,f) = u ++ " : " ++ showFormula f ++ "\n"

showAssi :: Assi -> String
showAssi assi = 
 "\n"++concat [u ++ " |-> "++ (if b then "1" else "0") ++ "\n" | (u,b) <- assi ]

showPP :: PlProof -> String -> String
showPP pp commandtext =
--   latexdoc (latexPartialProof pp ++ 
   latexdoc ("\\input{currentPP.tex}" ++  -- latexdoc in Buss.hs
                if null (goalstack pp)
                then "\\bigskip\n\n Proof complete."
                else commandtext)



showError :: Err -> String
showError err =
  case err of
    IncorrectTermE     -> "Incorrect term, try again"
    IncorrectFormE     -> "Incorrect formula, try again"
    NoTextExpE         -> "No text expected, try again"
    UnknownAssuE       -> "Assumption doesn't fit or doesn't exist, try again"
    RuleNotApplicableE -> "Rule not applicable, try again"
    ProofCompleteE     -> "Proof complete, nothing to do"
    TextExpE           -> "Text input expected, try again"
    RefinementE s      -> "Failed to refine: " ++ s    

welcometextLong :: String
welcometextLong =
  "{\\large\\em Welcome to the Interactive Prawf}\n\n" ++
  "\\bigskip\n\n" ++
  "Please provide your details to start.\n\n" ++
  "\\bigskip\n\n" ++
  "The input syntax is explained by the following example:\n" ++
  "\\begin{center}\n" ++
  "\\verb|A and B  -> A or (B and not C) -> bot|" ++ 
  "\\end{center}\n\n" ++
  "\\begin{itemize}\n" ++ 
  "\\item Instead of \\verb|and| you may use \\verb|&|,\n " ++
  "\\item instead of \\verb|not A| you may write \\verb|A -> bot|,\n" ++
  "\\item instead of \\verb|bot| (falsity) you may write \\verb|F|.\n" ++
  "\\end{itemize}\n" ++ 
  "The usual conventions for omitting parentheses apply.\n\n" ++
  "Hence, the formula above is the same as\n" ++
  "\\begin{center}\n" ++
  "\\verb|(A & B) -> ((A or (B & (C -> F))) -> F)|" ++ 
  "\\end{center}\n\n" ++
  "\\bigskip\n\n" ++
  "Type \\verb|undo| to undo a proof step." ++
  "\\bigskip\n\n" ++
  "Type \\verb|quit| to leave the prover." ++
  "\\bigskip\n\n" ++
  "Type \\verb|help| for more help."

commandtextLong :: String
commandtextLong =
  "\\bigskip\n\n" ++
  "Proof commands " ++
  "(in backwards reasoning mode): \n" ++
  "\\begin{center}\n" ++
  "\\begin{tabular}{lll}\n" ++
  "\\verb|use u|  & use assumption \\verb|u| & \\\\ \n" ++
  "\\verb|andi|   & And introduction & $\\land^+$\\\\ \n" ++
  "\\verb|andel|  & And elimination left     & $\\land^-_l$\\\\ \n" ++
  "\\verb|ander|  & And elimination right    & $\\land^-_r$\\\\ \n" ++
  "\\verb|impi| & Implication introduction & $\\to^+u$\\\\ \n" ++
  "\\verb|impi u| & Implication introduction with a label for the premise& $\\to^+u$\\\\ \n" ++
  "\\verb|impe|   & Implication elimination  & $\\to^-$\\\\ \n" ++
  "\\verb|impe A|   & Implication elimination with premise & $\\to^-$\\\\ \n" ++
  "\\verb|oril|   & Or introduction left     & $\\lor^+_l$\\\\ \n" ++
  "\\verb|orir|   & Or introduction right    & $\\lor^+_r$\\\\ \n" ++
  "\\verb|ore|    & Or elimination           & $\\lor^-$\\\\ \n" ++
  "\\verb|ore A or B| & Or elimination with selected disjunction          & $\\lor^-$\\\\ \n" ++
  "\\verb|efq|    & ex-falso-quodlibet       & efq\\\\ \n" ++
  "\\verb|raa|    & reductio-ad-absurdum     & raa\\\\ \n" ++
{-
  "\\verb|alli|   & All introduction         & $\\forall^+$\\\\ \n" ++
--  "\\verb|alle all x A(x)|   & All elimination with a quantified formula & $\\forall^-$\\\\ \n" ++
  "\\verb|alle|   & All elimination (enter term) & $\\forall^-$\\\\ \n" ++
  "\\verb|alle t|   & All elimination with term to be genralised & $\\forall^-$\\\\ \n" ++
--  "\\verb|allef|  & All elimination (enter $\\forall$-formula)  & $\\forall^-$\\\\ \n" ++
  "\\verb|exi|    & Ex introduction          & $\\exists^+$\\\\ \n" ++
  "\\verb|exi t|  & Ex introduction with a term to substitute the bound variable  & $\\exists^+$\\\\ \n" ++
  "\\verb|exe|    & Ex elimination           & $\\exists^-$\\\\ \n" ++
  "\\verb|exe ex x A(x)|    & Ex elimination with an existential formula    & $\\exists^-$\\\\ \n" ++
-}
  "\\end{tabular}\n" ++
  "\\end{center}\n" ++
  "Control commands:\n" ++
  "\\begin{center}\n" ++
  "\\begin{tabular}{ll}\n" ++
  "\\verb|undo| & undo a proof step \\\\ \n" ++
  "\\verb|quit| & leave the prover \\\\ \n" ++
--  "\\verb|save <filename>| & save your current proof (and begin a new proof) \\\\ \n" ++
  "\\verb|new| & start a new proof (without saving your current proof)\\\\ \n" ++
  "\\verb|submit |$i$ & submit curent proof as solution to question $i$\\\\ \n"  ++
--  "\\verb|delete |$i$ & delete question $i$\\\\ \n"  ++
--  "\\verb|size <i> <size>|& display Question \\verb|<i>| in size \\verb|<size>| where \\verb|<size>| can have the values\\\\ \n"++
--  "    &\\verb|small|, \\verb|footnotesize|, \\verb|tiny|, \\verb|normal|\\\\ \n" ++
  "\\verb|?| & more explanations on the commands above \n" ++
  "\\end{tabular}\n" ++
  "\\end{center}\n" ++
--  "User Manual: " -- ++
  "See the \\verb|USER-MANUAL| for details about how to use the proof rules."

--  "\\texttt{https://https://prawftree.files.wordpress.com/2016/09/prawf\\_usermanual.pdf}"
--  "\\url{https://prawftree.files.wordpress.com/2016/09/usermanual.pdf}"
  -- "\\For more information refer to the \\href{bit.ly/2d4EgmJ}{User Manual}"
  --"Your assignment will be created as a pdf file named " ++
  --"\\verb|assignment_<level>_<stdno>.pdf|." 


{--showTerm :: Term -> String
showTerm t = case t of
   {
    Const c    -> c;
    Var x      -> x;
    Fun fun ts -> if (fun `elem` infixfunnames) && (length ts == 2)
                  then showTermB (ts!!0) ++ fun ++ showTermB (ts!!1)
                  else fun ++ " (" ++ (intercalate "," (map showTerm ts)) ++ ") "
   }
   
showTermB :: Term -> String
showTermB t@(Fun fun ts) = 
    if (fun `elem` infixfunnames)
    then "(" ++ showTerm t ++ ")"
    else showTerm t
showTermB t = showTerm t 
   
showTerms :: [Term] -> String
showTerms [] = []
showTerms (t:ts) = 
  "(" ++ showTerm t ++ concat ["," ++ showTerm s |  s <- ts] ++ ")"
--}
showFormula' :: Formula -> String
showFormula' f = showF f ""


-- This is wrong!!! (parentheses missing)
showF :: Formula -> String -> String
showF (Atom p ts) str = p ++ (showTerms ts ++ str)
showF (And f1 f2) str = showF f1 (" & " ++ showF f2 str)
showF (Or f1 f2) str = showF f1 (" v " ++ showF f2 str)
showF (Imp f1 f2) str = showF f1 (" -> " ++ showF f2 str)
showF (Bot) str = "False" ++ str
showF (All x f) str = "All " ++ x ++ " " ++ showF f str
showF (Ex x f) str = "Ex " ++ x ++ " " ++ showF f str
