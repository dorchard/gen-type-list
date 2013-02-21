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

> import Data.Generics.Uniplate.Operations
> import Data.Generics.Uniplate.Data

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
>        return $ [ClassD [] name' (map PlainTV (params ++ result)) [funDep] 
>                  [SigD name (convTyp (params ++ result) typ)]]

> interpretDec (FunD name clauses) = 
>     do clauses' <- mapM (interpretClause name) clauses
>        return $ concat clauses'


Funny how these two are very similar- shame there is no
way to abstract this in Haskell.

 convExp :: Exp -> Q Exp
 convExp (ConE n) | nameBase n == ":" = [| HNil |]
                   | nameBase n == "[]" = [| HCons |]
                   | otherwise = return $ ConE n
 convExp (ListE xs) = go xs 
                        where go [] = [| HNil |]
                              go (x:xs) = [| HCons $(return x) $(go xs) |]
 convExp x = return x

 convPat :: Pat -> Q Pat
 convPat (ConP n ps) | nameBase n == ":" = [p| HNil |]
                     | nameBase n == "[]" = return $ ConP (mkName "HCons") ps
                     | otherwise = return $ ConP n ps
 convPat (ListP xs) = go xs 
                        where go [] = [p| HNil |]
                              go (x:xs) = do y <- go xs 
                                             return $ ConP (mkName "HCons") [x,  y]
 convPat x = return x

> convExp :: Exp -> Q Exp
> convExp e@(ConE n) | nameBase n == ":" = [| HCons |]
>                    | nameBase n == "[]" = [| HNil |]
>                    | otherwise = return e
> convExp (ListE xs) = foldr (appE . (appE [| HCons |]) . return) [| HNil |] xs
> convExp x = return x

> convPat :: Pat -> Q Pat
> convPat (ConP n ps)       | nameBase n == ":" = return $ ConP (mkName "HCons") ps
>                           | nameBase n == "[]" = [p| HNil |]
> convPat (UInfixP p1 n p2) | nameBase n == ":" = return $ ConP (mkName "HCons") [p1, p2]
> convPat (InfixP p1 n p2)  | nameBase n == ":" = return $ ConP (mkName "HCons") [p1, p2]
> convPat (ListP xs) = foldr (\x -> \y -> conP (mkName "HCons") [return x,y]) [p| HNil |] xs
> convPat x = return x


> convTyp :: [Name] -> Type -> Type
> convTyp [x] _ = VarT x
> convTyp xs (ForallT _ _ t) = convTyp xs t
> convTyp (x:xs) (AppT (AppT ArrowT t1) t2) = AppT (AppT ArrowT (VarT x)) (convTyp xs t2)
> convTyp xs t = t

> patToTyp :: Pat -> Q Type
> patToTyp (VarP name) = return $ VarT name
> patToTyp (UInfixP p1 n p2) = 
>     if (nameBase n == ":") then 
>      do p1' <- patToTyp p1
>         p2' <- patToTyp p2
>         return $ AppT (AppT (ConT $ mkName "HCons") p1') p2'
>     else error "Patterns on lists only"
> patToTyp (ConP n []) = if (nameBase n == "[]") then 
>                          return $ ConT (mkName "HNil")
>                        else error "Patterns on lists only"
> patToTyp (ListP []) = return $ ConT (mkName "HNil")
> patToTyp (WildP) = do n <- newName "w"
>                       return $ VarT n
> patToTyp (ParensP p) = patToTyp p
> patToTyp p = error $ "Can't understand pattern: " ++ (show p)
>             

> interpretClause :: Name -> Clause -> Q [Dec]
> interpretClause name (Clause pats (NormalB exp) []) =
>     do pats' <- mapM patToTyp pats
>        let name' = mkName . camelCase . show $ name
>        let typ = foldl AppT (ConT name') (pats' ++ [VarT (mkName "res")])
>        exp' <- transformM convExp exp
>        pats' <- mapM (transformM convPat) pats
>        return $ [InstanceD [] typ [FunD name [Clause pats' (NormalB exp') []]]]
        
>        --[d| class $(camelCase name) $(params) |] -- | $(params) -> $(result) 

>     
>     
>         