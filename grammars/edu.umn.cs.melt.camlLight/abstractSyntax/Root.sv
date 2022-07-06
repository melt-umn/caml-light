grammar edu:umn:cs:melt:camlLight:abstractSyntax;


type TyCtxType = [Pair<String Type>];


--A list of known atomic types
restricted inherited attribute knownTypes::[Pair<String ExtantType>];

--A list of known names, including constructors
--This needs to be implicit because the type attribute flows into it
implicit inherited attribute gamma::Maybe<TyCtxType>;

--A list of type substitutions for type variables
--Why is this an implicit Maybe?  This allows us to use the implicit
--   type to decide what this will be.
implicit inherited attribute subst::Maybe<[Pair<String Type>]>;

--A list of constructors and their types
restricted inherited attribute knownConstructors::[Pair<String Type>];


--find out whether a given type is real and how many parameters it has
function lookupType
Maybe<ExtantType> ::= tyname::String knownTypes::[Pair<String ExtantType>]
{
  return case knownTypes of
         | [] -> nothing()
         | pair(name, et)::tl -> if tyname == name
                                 then just(et)
                                 else lookupType(tyname, tl)
         end;
}


--find the type for a given name
function lookupName
Maybe<Type> ::= name::String gamma::[Pair<String Type>]
{
  return case gamma of
         | [] -> nothing()
         | pair(n, ty)::tl -> if name == n
                              then just(ty)
                              else lookupName(name, tl)
         end;
}
function lookupName_default
Type ::= name::String gamma::[Pair<String Type>] d::Type
{
  return case lookupName(name, gamma) of
         | nothing() -> d
         | just(t) -> t
         end;
}



--the updated contexts after a declaration
implicit synthesized attribute gamma_out::Maybe<TyCtxType>;
restricted synthesized attribute knownTypes_out::[Pair<String ExtantType>];
implicit synthesized attribute subst_out::Maybe<[Pair<String Type>]>;
restricted synthesized attribute knownConstructors_out::[Pair<String Type>];



restricted synthesized attribute defOK::Boolean;


nonterminal ExceptionDef with
   pp, knownConstructors, knownConstructors_out, defOK, knownTypes;

abstract production excDef
top::ExceptionDef ::= c::Constructors
{
  top.pp = "exception " ++ c.pp;

  restricted c.buildingType = exceptionType();

  restricted c.knownTypes = top.knownTypes;

  restricted c.knownTyVars = [];

  restricted c.knownConstructors = top.knownConstructors;
  restricted top.knownConstructors_out = c.knownConstructors_out;

  restricted top.defOK = c.defOK;
}



--This is the information to be printed out at the top for the whole file
--It will include the definitions and expression types
synthesized attribute output::String;


nonterminal TopLevel with pp, gamma, knownTypes, knownConstructors, output;

abstract production excDefTopLevel
top::TopLevel ::= e::ExceptionDef rest::TopLevel
{
  top.pp = e.pp ++ ";;\n\n" ++ rest.pp;

  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = e.knownConstructors_out ++ top.knownConstructors;

  implicit rest.gamma = top.gamma;

  top.output = "Exception Def:\n" ++
               ( if !e.defOK
                 then "Exception definition failed"
                 else implode(", ", map(\p::Pair<String Type> ->
                      fst(p), e.knownConstructors_out)) ) ++ "\n\n" ++ rest.output;
}


abstract production tyDefTopLevel
top::TopLevel ::= t::TypeDefinition rest::TopLevel
{
  top.pp = t.pp ++ ";;\n\n" ++ rest.pp;

  implicit rest.gamma = top.gamma;

  restricted t.knownTypes = top.knownTypes;
  restricted rest.knownTypes = t.knownTypes_out ++ top.knownTypes;

  restricted t.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = t.knownConstructors_out ++ top.knownConstructors;

  top.output = "Type Def:\n" ++
               ( if t.defOK
                 then knownTypes_ToString(t.knownTypes_out)
                 else "Error in defining types [" ++ implode(", ", t.tyNames) ++ "]") ++
               "\n\n" ++ rest.output;
}


abstract production exprTopLevel
top::TopLevel ::= e::Expr rest::TopLevel
{
  top.pp = e.pp ++ ";;\n\n" ++ rest.pp;

  implicit e.gamma = top.gamma;
  implicit rest.gamma = top.gamma;

  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  implicit e.subst = [];

  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  top.output = "Expression:\n   " ++ e.pp ++ "\n" ++
               "Type:\n   " ++ case e.type, e.subst_out of
                               | just(ty), just(subs) -> typePrettify(typeSubst(ty, subs)).pp
                               | _, _ -> "Type does not exist"
                               end ++ "\n\n" ++
               rest.output;
}


abstract production topLevelEnd
top::TopLevel ::=
{
  top.pp = "";

  top.output = "";
}




nonterminal Root with pp, output;

abstract production root
top::Root ::= t::TopLevel
{
  top.pp = t.pp;

  --initial known type names (built-in types)
  restricted t.knownTypes = [pair("list", inductiveExtant(1)),
                             pair("reference", inductiveExtant(1)),
                             pair("array", inductiveExtant(1))];

  implicit t.gamma = [];

  --initial known named constructors
  restricted t.knownConstructors = [pair("true", boolType()),
                                    pair("false", boolType()),
                                    pair("Invalid_argument", exceptionType())];

  top.output = t.output;
}

