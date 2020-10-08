# caml-light

This is an implementation of the Caml Light language using Silver.  In
particular, it shows the use of implicit monads, which allows
attributes of a monadic type to be used as if they were not of a
monadic type (e.g. the `type` attribute of type `Maybe<Type>` can be
used as if it had type `Type`).

