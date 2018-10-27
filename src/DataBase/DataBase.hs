

data Pair a b = Pair a b 
  deriving Eq 
data Maybe a = Nothing | Just a 
  deriving Eq 

data Fun a b = Fun b [Pair a b]
  deriving Eq 

{-@ reflect applyFun @-}
applyFun :: Eq a => (Fun a b) -> a -> b 
applyFun (Fun d []) _ = d 
applyFun (Fun d (Pair k v:kvs)) k' 
  | k == k' = v
  | otherwise = applyFun (Fun d kvs) k' 



 

type DB l  = [Pair TName (Table l)]
data Row l = Row { rowKey :: Term l, rowField1 :: Term l, rowField2 :: Term l}
{-@ data Row l = Row { rowKey    :: {t:Term l | isDBValue t && ςTerm t } 
                     , rowField1 :: {t:Term l | isDBValue t && ςTerm t } 
                     , rowField2 :: {t:Term l | isDBValue t && ςTerm t } } @-}
-- {-@ data Row l = Row { rowKey    :: {t:Term l | isDBValue t || t == THole}
--                      , rowField1 :: {t:Term l | isDBValue t || t == THole}
--                      , rowField2 :: {t:Term l | isDBValue t || t == THole} } @-}

  deriving Eq 
data TInfo l = TInfo {tableLabel :: l, keyLabel :: l, field1Label :: l, field2Label :: Fun (Term l) l, uniquiInt :: Int}
{-@ data TInfo l = TInfo { tableLabel  :: l
                         , keyLabel    :: l
                         , field1Label :: {l:l | canFlowTo l tableLabel }
                         , field2Label :: Fun (Term l) l
                         , uniquiInt   :: Int } @-}
  deriving Eq 

data Table l = Table {tableInfo :: (TInfo l), tableRows :: [Row l]}
  deriving Eq 
{-@ data Table l = Table {tableInfo :: (TInfo l), tableRows :: [Row l]} @-}


-- Be careful: LH is bad with curring: use makeValLable instead of valLabel!!!!
{-@ reflect makeValLabel @-}
{-@ makeValLabel :: ti:TInfo l -> t:Term l -> {l:l | l == applyFun  (field2Label ti) t} @-}
makeValLabel :: (Eq l, Label l) =>  TInfo l -> Term l -> l
makeValLabel ti t = applyFun (field2Label ti) t  


{-@ reflect εDB @-}
εDB :: (Eq l, Label l) =>  l -> DB l -> DB l 
εDB l []     = [] 
εDB l (Pair n t:ts) = Pair n (εTable l t):εDB l ts 

{-@ reflect εTable @-}
εTable :: (Eq l, Label l) =>  l -> Table l -> Table l 
εTable l (Table ti r) 
  | not (tableLabel ti `canFlowTo` l)
  = Table ti [] 
  | otherwise
  = Table ti (εRows l ti r) 

{-@ reflect εRows @-}
{-@ εRows :: (Eq l, Label l) =>  l -> TInfo l -> rs:[Row l] -> {v:[Row l] | len v == len rs} @-} 
εRows :: (Eq l, Label l) =>  l -> TInfo l -> [Row l] -> [Row l] 
εRows l ti [] = [] 
εRows l ti (r:rs) = εRow l ti r:εRows l ti rs  

{-@ reflect εRow @-}
-- εRow :: (Eq l, Label l) =>  l -> TInfo l -> Row l -> Row l 
-- εRow l ti r@(Row k THole v2) = r
-- -- εRow l ti (Row k THole v2) = Row k THole THole
-- εRow l ti (Row k v1 v2) = Row k v1' v2'
--     where
--         v1' = if field1Label ti `canFlowTo` l then v1 else THole
--         v2' = if makeValLabel ti v1 `canFlowTo` l then v2 else THole -- JP: What if v1 is a hole?

-- JP: Maybe we should make this return the v2 if v1 is THole?
εRow l ti (Row k v1 v2) | not (field1Label ti `canFlowTo` l) = Row k THole THole
εRow l ti (Row k v1 v2) = 
-- JP: Weren't we talking about propagating erasure here? It shouldn't matter since erasure is the identity for database values in practice. XXX
    if makeValLabel ti v1 `canFlowTo` l then
        Row k (εTerm l v1) (εTerm l v2) 
    else
        Row k (εTerm l v1) THole 

