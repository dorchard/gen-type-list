> {-# LANGUAGE TemplateHaskell #-}

> module Gen where
>     
> import Language.Haskell.TH
> import Language.Haskell.TH.Quote
> import Language.Haskell.Meta.Parse

> import Control.Monad.State.Lazy

> import Data.Char

> import Data.HList
> import Data.HList.HListPrelude

> import Debug.Trace

> gen = QuasiQuoter { quoteDec = parseDec }

> parseDec :: String -> Q [Dec]
> parseDec input = do loc <- location
>                     let pos = (loc_filename loc,
>                                fst (loc_start loc),
>                                snd (loc_start loc))
>                     case (parseDecs input) of
>                       Left msg -> error msg
>                       Right def -> interpret def


> clausePat :: Clause -> [Pat]
> clausePat (Clause p _ _) = p

> clauseBody :: Clause -> Body
> clauseBody (Clause _ b _) = b

arity :: [Clause] -> Int
arity = maximum . (map (\(Clause p _ _) -> length p))

> camelCase :: String -> String
> camelCase [] = []
> camelCase (x:xs) = (toUpper x) : xs

> interpret :: [Dec] -> Q [Dec]
> interpret ds = do decs <- mapM interpretDec ds
>                   return $ concat decs
>   

> arity :: Type -> Int
> arity (AppT (AppT ArrowT t1) t2) = 1 + arity t2
> arity (ForallT _ _ t) = arity t
> arity _ = 0              

> interpretDec :: Dec -> Q [Dec]
> interpretDec (SigD name typ) = 
>     do let params = map (mkName . ("p"++) . show) [0..((arity typ) - 1)]
>        let result = [mkName "res"]
>        let funDep = (FunDep params result)
>        let name' = mkName . camelCase . show $ name
>        return $ [ClassD [] name' (map PlainTV (params ++ result)) [funDep] []]

> interpretDec (FunD name clauses) = 
>     do let name' = mkName . camelCase . show $ name
>        clauses' <- mapM (interpretClause name') clauses
>        return $ concat clauses'

> convPat :: Pat -> Q Type
> convPat (VarP name) = return $ VarT name
> convPat (UInfixP p1 n p2) = 
>     if (nameBase n == ":") then 
>      do p1' <- convPat p1
>         p2' <- convPat p2
>         return $ AppT (AppT (ConT $ mkName "HCons") p1') p2'
>     else error "Patterns on lists only"
> convPat (ConP n []) = if (nameBase n == "[]") then 
>                          return $ ConT (mkName "HNil")
>                       else error "Patterns on lists only"
> convPat (ListP []) = return $ ConT (mkName "HNil")
> convPat (WildP) = do n <- newName "w"
>                      return $ VarT n
> convPat (ParensP p) = convPat p
> convPat p = error $ "Can't understand pattern: " ++ (show p)
>             

> interpretClause :: Name -> Clause -> Q [Dec]
> interpretClause name (Clause pats (NormalB exp) []) =
>     do pats' <- mapM convPat pats
>        let typ = foldl AppT (ConT name) (pats' ++ [VarT (mkName "res")])
>        return $ [InstanceD [] typ []]
        
>        --[d| class $(camelCase name) $(params) |] -- | $(params) -> $(result) 

>     
>     
>         