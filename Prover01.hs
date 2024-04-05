module Prover
-- ==================================
-- Main application module (for Linux)

-- controls the user's interaction with the system allowing the user to apply 
-- the rules of natural deduction in the backwards fashion
-- ==================================
-- getDetails loop displayState transPP  latexPP quitProcess 
-- helpProcess saveProcess submitProcess submitsize assignmentProcess 
-- question solution displayError

  where

import Perhaps
import Parser
import Formula
import Proof
import Buss
import Step
import ReadShow

-- import GHC.IOBase
import GHC.IO
import System.Process

import SystemL   -- Linux
-- import SystemW   -- Windows

main :: IO ()
main = do {
           writeFile "pproof.tex" (latexdoc welcometextLong) ;
           displayPP;  -- SystemL 
           watchPP;    -- SystemL
           getDetails ;
           loop (startState,[])
          }

main0 :: IO ()  -- use if xdvi window is already open
main0 = do {
           writeFile "pproof.tex" (latexdoc welcometextLong) ;
           displayPP; 
           loop (startState,[])
          }


main1 :: IO ()  -- use if xdvi window is closed, but you had a session earlier
main1 = do {
           writeFile "pproof.tex" (latexdoc welcometextLong) ;
           displayPP; 
           watchPP;
           loop (startState,[])
          }

getDetails :: IO ()
getDetails = 
      do {
           putStr "Please enter your name: " ;
           myname <- getLine ;
           putStr "Please enter your student number: " ;
           mystno <- getLine ;
           putStr "Please enter your level of study (3 or M): " ;
           mylevel <- getLine ;
           writeFile "name.tex" myname ;
           writeFile "stno.tex" mystno ;
           writeFile "level.tex" mylevel ;
           let {myfilename = "assignment_"++mylevel++"_"++mystno++".tex"} ;
           writeFile "myfilename.txt" myfilename ;
           syscopy "assignment0.tex" myfilename;
           runpdflatex myfilename ;
           return () 
         }


loop :: (State,[State]) -> IO ()
loop (state@(out,ips,pp,n),his) =
  do {
       displayState state  ;
       s <- getLine ;
       case words s of
        {
         ["quit"]    -> quitProcess state ;
         ["help"]    -> helpProcess >> loop (state,his) ;
         ["save",fn] -> saveProcess fn >> loop (state,his) ;
         ["new"]     -> loop (startState,[]) ;
         ["undo"]    -> case his of
                         { 
                          (state0:his') -> loop (state0,his') ;
                          []            -> loop (startState,[])
                         } ;
         ["submit",i] -> submitProcess i >> loop (state,his) ;
         ["delete",i] -> writeFile (question i) "" 
                         >> (readFile "myfilename.txt"  >>= runpdflatex) 
                         >> loop (state,his) ;
         ["size", i, mysize] -> submitsize i mysize >> loop (state,his) ;
         ("?":ws) -> putStrLn (helptext ws) >> loop (state,his) ; 
         _            -> loop (steps (str2Inputs s) state, state:his) 
        } 
    }

displayState :: State -> IO ()
displayState state =  
  do {
       exec latexPP (transPP state) ;  -- exec in Perhaps
       displayPP ;
       putStr (showState state ++ "> ")
     }

transPP :: State -> Perhaps PlProof
transPP (_,ips,pp,n) =
 case ips of 
  {
   ImpeS  -> let { [gl1,gl2] = newGoalSymbols n 2 } 
             in refine pp (ImpElimBW gl1 gl2 (Atom "X" []));
   AndelS -> let { [gl] = newGoalSymbols n 1 } 
             in refine pp (AndElilBW gl (Atom "X" []));
   AnderS -> let { [gl] = newGoalSymbols n 1 } 
             in refine pp (AndElirBW gl (Atom "X" []));
   OreS   -> let { [gl1,gl2,gl3] = newGoalSymbols n 3 } 
             in refine pp (OrElimBW gl1 gl2 gl3 (Or (Atom "X" []) (Atom "Y" [])));
   AlleS  -> let { [gl] = newGoalSymbols n 1}
             in refine pp (AllElimBWX gl (All "?x" (Atom "X" [])));
   ExeS   -> let { [gl1, gl2] = newGoalSymbols n 2 }
             in refine pp (ExElimBW gl1 gl2 (Ex "?x" (Atom "X" [])));
   _      -> Success pp 
  }

latexPP :: PlProof -> IO()
latexPP pp = 
  do { 
       writeFile "pproof.tex" (showPP pp commandtextLong) ;  -- ReadShow
       writeFile "currentPP.tex" (latexPartialProof pp)
     }
             
quitProcess :: State -> IO ()
quitProcess _ = return ()  -- to be improved

helpProcess :: IO ()
helpProcess = putStrLn "Please consult the User Manual at https://prawftree.files.wordpress.com/2016/09/usermanual.pdf"

saveProcess :: String -> IO ()
saveProcess fn = do { f <- readFile "currentPP.tex" ; writeFile fn f }

submitProcess :: String -> IO ()
submitProcess i = syscopy "currentPP.tex" (solution i) >> submitsize i "normal" 

submitsize :: String -> String -> IO ()
submitsize i size =
  do {    
       proof <- readFile (solution i) ;
       writeFile (question i) 
                 ("\\bigskip\\bigskip\n\n{\\bf Question " 
                  ++ i 
                  ++ ".}\\medskip\n\n" 
                  ++ latexenvnl size proof) ;
       readFile "myfilename.txt"  >>= runpdflatex ;
       return ()
      }

assignmentProcess :: IO ()
assignmentProcess =
 do {
      myfilename <- readFile "myassignment.txt" ;     
      syscopy "assignment0.tex" myfilename ;
      system ("pdflatex " ++ myfilename );-- ++ " > /dev/null") ; 
      return ()
    }
  

question, solution :: String -> String
question i = "q0" ++ i ++ ".tex" 
solution i = "s0" ++ i ++ ".tex" 



displayError :: Err -> IO ()
displayError err = putStr (showError err ++ "> ")
