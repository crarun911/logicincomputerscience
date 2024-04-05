import Control.Concurrent

sq :: Int -> IO ()
sq x = let { s = show (x^2)}
       in putStrLn s >> appendFile "OUT.txt" s 

delay :: Int -> IO a -> IO a
delay c m = threadDelay c >> m
{-
  do {
       threadDelay c ;
       v <- m ;
       return v
     }
-}

main :: IO ()
main = loop 20
 where
  loop n = if n <= 0 
           then return ()
           else do { 
                     s <- readFile "IN.txt"; 
                     sq (read s) ; 
                     threadDelay 2000000;
                     (loop (n-1)) 
--                     delay 2000000 (loop (n-1)) 
                   }

-- possibly better use System.IO.Strict

writeFileStrict :: String -> String -> IO ()
writeFileStrict fn s =
  do {
       writeFile fn s ;
       s' <- readFile fn ;
       length s' `seq` return ()
     }

readFileStrict :: String -> IO String
readFileStrict fn =
  do {
       s <- readFile fn ;
       length s `seq` return s
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



-- reads file fn and, unless stop, does action act with its content, 
-- but only if file has changed. The file is checked every d time units.
watch :: Int -> (String -> Bool) -> String -> (String -> IO a) -> IO ()
watch d stop fn act = loop ""
 where
   loop s = do {
                 s' <- readFile fn ;
                 if s == s' ;
                 then threadDelay d >> loop s ;
                 else if stop s'
                      then return ()
                      else act s' >> loop s'
               }

-- watch and print                 
wp :: IO ()
wp = watch 100000 (\s-> length s > 3) "IN.txt" putStrLn                 

{-
http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Concurrent.html
Control.Concurrent

threadDelay :: Int -> IO ()

Suspends the current thread for a given number of microseconds (GHC only).

There is no guarantee that the thread will be rescheduled promptly when the delay has expired, but the thread will never continue to run earlier than specified.



http://hackage.haskell.org/package/base-4.12.0.0/docs/System-IO.html
System.IO

hWaitForInput :: Handle -> Int -> IO Bool

Computation hWaitForInput hdl t waits until input is available on handle hdl. It returns True as soon as input is available on hdl, or False if no input is available within t milliseconds. Note that hWaitForInput waits until one or more full characters are available, which means that it needs to do decoding, and hence may fail with a decoding error.

If t is less than zero, then hWaitForInput waits indefinitely.

This operation may fail with:

    isEOFError if the end of file has been reached.
    a decoding error, if the input begins with an invalid byte sequence in this Handle's encoding.

NOTE for GHC users: unless you use the -threaded flag, hWaitForInput hdl t where t >= 0 will block all other Haskell threads for the duration of the call. It behaves like a safe foreign call in this respect.
-}