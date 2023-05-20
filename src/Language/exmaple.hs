
safe-divM :: Maybe Int -> Maybe Int -> Maybe Int
safe-divM (Just _) (Just 0) = Nothing
safe-divM (Just x) (Just y) = Just (x / y)
safe-divM _ _ = Nothing

safe-divE :: Either String Int -> Either String Int -> Either String Int
safe-divE (Right _) (Right 0) = Left ""
safe-divE (Right x) (Right y) = Right (x / y)
safe-divE _ _ = Left ""
