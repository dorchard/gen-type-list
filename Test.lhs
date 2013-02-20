> {-# LANGUAGE QuasiQuotes #-}
> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE UndecidableInstances #-}

> import Gen
> import Data.HList

> [gen|
>  append :: [a] -> [a] -> [a]
>  append [] xs = xs
>  append (x:xs) ys = x : (append xs ys)
> |]