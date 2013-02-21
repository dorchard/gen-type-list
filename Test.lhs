> {-# LANGUAGE QuasiQuotes #-}
> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE FlexibleInstances #-}

> import Gen
> import Data.HList hiding (append)

> [gen|
>  append :: [a] -> [a] -> [a]
>  append [] xs = xs
>  append (x:xs) ys = x : (append xs ys)
> |]