-- !!!!!!!!!!!!!!!!!!!!!!
-- currently user input via file IN.txt
-- see below readNEF and getUserInput
-- to change back to terminal input 
-- switch then commenting out of getUserInput
-- !!!!!!!!!!!!!!!!!!!!!!
module Prover
-- ==================================
-- Main application module (for Linux)

-- controls the user's interaction with the system allowing the user to apply 
-- the rules of natural deduction in the backwards fashion
-- ==================================
-- getDetails loop displayState transPP  latexPP quitProcess 
-- helpProcess saveProcess submitProcess submitsize 
-- question solution displayError

  where

import Control.Concurrent

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
--import SystemW   -- Windows

main :: IO ()  -- use if xdvi window is already open
main = loop (startState,[])
         
{-
main :: IO ()
main = do {
           writeFile "pproof.tex" (latexdoc welcometextLong) ;
           displayPP;  -- SystemL 
           watchPP;    -- SystemL
           getDetails ;
           loop (startState,[])
          }
-}


main0 :: IO ()  -- use if xdvi window is already open
main0 = do {
--           writeFile "pproof.tex" (latexdoc welcometextLong) ;
--           displayPP; 
          loop (startState,[])
          }


main1 :: IO ()  -- use if xdvi window is closed, but you had a session earlier
main1 = do {
           writeFile "pproof.tex" (latexdoc welcometextLong) ;
           displayPP; 
           watchPP;
           loop (startState,[])
          }


-- getDetails switched off
{-
getDetails :: IO ()
getDetails = 
      do {
           let {myname = "Kurt Goedel"} ;
           let {mystno = "123456"} ;
           let {mylevel = "G"} ;
           writeFile "name.tex" myname ;
           writeFile "stno.tex"  mystno ;
           writeFile "level.tex" mylevel ;
           let {myfilename = "assignment_"++mylevel++"_"++mystno++".tex"} ;
           writeFile "myfilename.txt" myfilename ;
           syscopy "assignment0.tex" myfilename;
           runlatex myfilename ;
           return () 
         }
-}


{-
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
           runlatex myfilename ;
           return () 
         }
-}

getDetails :: IO ()
getDetails = 
      do {
           putStr ("Please enter name, studtno, level of all contributors "
                 ++ " (max 3, all in one line):\n "
                 ++ "[Example: Kurt Goedel (3, 123456), Alan Turing (M, 234567)]\n") ;
           myname <- getLine ;
           writeFile "contributors.tex" myname ;
           runlatex "assignment.tex" ; -- runlatex in SystemL.hs
           return () 
         }


-- read nonempty file
readNEF :: Int -> String -> IO String
readNEF d fn = loop 
 where
  loop = 
    do {
         s <- readFile fn ;
         if length s == 0   -- forcing s
         then threadDelay d >> loop ;
         else do {
                   writeFile fn "" ; 
                   s' <-readFile fn ; 
                   if length s' == 0 -- forcing s'
                   then return s
                   else error "readNF" 
                 }
       }

getUserInput :: IO String
getUserInput = getLine   -- command line mode
-- getUserInput = readNEF 10000 "IN.txt" -- file mode

loop :: (State,[State]) -> IO ()
loop (state@(out,ips,pp,xs,n),his) =
  do {
       displayState state  ;
       s <- getUserInput ;
       case words s of
        {
         ["quit"]    -> quitProcess state ;
         ["help"]    -> helpProcess >> loop (state,his) ;
         ["save",fn] -> saveProcess fn >> loop (state,his) ;
         ["deriv",fn] -> writeFile fn (show pp ++"\n\n"++ show xs) 
                                       >> loop (state,his) ;
         ["new"]     -> loop (startState,[]) ;
         ["undo"]    -> case his of
                         { 
                          (state0:his') -> loop (state0,his') ;
                          []            -> loop (startState,[])
                         } ;
         ["submit",i] -> submitProcess i >> 
                         runlatex "assignment.tex" >> 
                         loop (state,his) ;
         ["delete",i] -> writeFile (question i) "" 
                         >> runlatex "assignment.tex" 
                         >> loop (state,his) ;
         ["size", i, mysize] -> submitsize i mysize >> loop (state,his) ;
         ("?":ws) -> putStrLn (helptext ws) >> loop (state,his) ; 
         _            -> loop (steps (str2Inputs s) state, state:his) 
        }                --    Step   ReadShow
    }

displayState :: State -> IO ()
displayState state =  
  do {
--     exec latexPP (transPP state) ;  -- exec in Perhaps
--       displayPP ;  -- SystemL
       putStr (showState state ++ "> ")  -- showState in ReadShow
     }

transPP :: State -> Perhaps PlProof
transPP (_,ips,pp,_,n) =
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
helpProcess = putStrLn (helptext []) -- helptext in ReadShow.hs
-- helpProcess = putStrLn "Please consult the User Manual at https://prawftree.files.wordpress.com/2016/09/usermanual.pdf"

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
       runlatex "assignment.tex" ;
       return ()
      }

question, solution :: String -> String
question i = "q0" ++ i ++ ".tex" 
solution i = "s0" ++ i ++ ".tex" 



displayError :: Err -> IO ()
displayError err = putStr (showError err ++ "> ")


clear :: [Int] -> IO ()
clear is = sequence_ [writeFile (question (show i)) "" | i <- is ]

-- Warning: the following deletes all solutions:
-- clear [1..20]
