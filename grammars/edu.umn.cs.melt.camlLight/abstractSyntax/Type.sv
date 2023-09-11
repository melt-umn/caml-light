grammar edu:umn:cs:melt:camlLight:abstractSyntax;


--whether the types are valid (nobody is throwing in an undefined type or using a type wrong)
restricted synthesized attribute validType::Boolean;
--variables that occur in a type
restricted synthesized attribute freeTyVars::[String];
--whether the type constructors are valid (new variables can be introduced)
restricted synthesized attribute validNewVarType::Boolean;

nonterminal Type with pp, knownTypes, knownTyVars, validType, freeTyVars, validNewVarType;

abstract production intType
top::Type ::=
{
  top.pp = "int";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production floatType
top::Type ::=
{
  top.pp = "float";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production boolType
top::Type ::=
{
  top.pp = "bool";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production charType
top::Type ::=
{
  top.pp = "char";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production stringType
top::Type ::=
{
  top.pp = "string";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production exceptionType
top::Type ::=
{
  top.pp = "exception";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production unitType
top::Type ::=
{
  top.pp = "unit";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}


abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = "(" ++ ty1.pp ++ ") -> " ++ ty2.pp;

  restricted ty1.knownTypes = top.knownTypes;
  restricted ty2.knownTypes = top.knownTypes;

  restricted ty1.knownTyVars = top.knownTyVars;
  restricted ty2.knownTyVars = top.knownTyVars;

  restricted top.validType = ty1.validType && ty2.validType;

  restricted top.validNewVarType = ty1.validNewVarType && ty2.validNewVarType;

  restricted top.freeTyVars = ty1.freeTyVars ++ ty2.freeTyVars;
}


abstract production tyVar
top::Type ::= name::String
{
  top.pp = "'" ++ name;

  --name is known to be a type variable
  restricted top.validType = containsBy(\x::String y::String -> x == y, name, top.knownTyVars);

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [name];
}


abstract production parameterizedTyConstructor
top::Type ::= tyl::[Type] name::String
{
  top.pp = if null(tyl)
           then name
           else "(" ++ foldr(\t::Type r::String -> r ++ "," ++ t.pp,
                             head(tyl).pp, tail(tyl)) ++ ") " ++ name;

  --known name, right number of parameters, and parameters are valid
  restricted top.validType =
             case lookupType(name, top.knownTypes) of
             | just(inductiveExtant(n)) ->
               if length(tyl) == n
               then foldr(\x::Type b::Boolean ->
                            b && decorate x with {knownTypes = top.knownTypes; knownTyVars = top.knownTyVars;}.validType,
                          true, tyl)
               else false
             | just(_) -> false
             | nothing() -> false
             end;

  restricted top.validNewVarType =
             case lookupType(name, top.knownTypes) of
             | just(inductiveExtant(n)) ->
               if length(tyl) == n
               then foldr(\x::Type b::Boolean ->
                            b && decorate x with {knownTypes = top.knownTypes;}.validNewVarType,
                          true, tyl)
               else false
             | just(_) -> false
             | nothing() -> false
             end;

  restricted top.freeTyVars = foldr(\a::Type l::[String] -> a.freeTyVars ++ l, [], tyl);
}



abstract production tupleType
top::Type ::= contents::TupleTyBuild
{
  top.pp = contents.pp;

  restricted contents.knownTypes = top.knownTypes;

  restricted contents.knownTyVars = top.knownTyVars;

  restricted top.validType = contents.validType;

  restricted top.validNewVarType = contents.validNewVarType;

  restricted top.freeTyVars = contents.freeTyVars;
}


nonterminal TupleTyBuild with pp, knownTypes, validType, freeTyVars, validNewVarType, knownTyVars;

abstract production tupleTyBuildAdd
top::TupleTyBuild ::= t::Type rest::TupleTyBuild
{
  top.pp = t.pp ++ " * " ++ rest.pp;

  restricted t.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted t.knownTyVars = top.knownTyVars;
  restricted rest.knownTyVars = top.knownTyVars;

  restricted top.validType = t.validType && rest.validType;

  restricted top.validNewVarType = t.validNewVarType && rest.validNewVarType;

  restricted top.freeTyVars = t.freeTyVars ++ rest.freeTyVars;
}


abstract production tupleTyBuildEnd
top::TupleTyBuild ::=
{
  top.pp = "";

  restricted top.validType = true;

  restricted top.validNewVarType = true;

  restricted top.freeTyVars = [];
}



--unify two types, yielding the unifying substitution
function typeUnify
[(String, Type)] ::= ty1::Type ty2::Type tySubs::[(String, Type)]
{
  return case typeSubst(ty1, tySubs) of
         | intType() -> case typeSubst(ty2, tySubs) of
                        | tyVar(x) -> (x, intType())::tySubs
                        | _ -> tySubs
                        end
         | floatType() -> case typeSubst(ty2, tySubs) of
                          | tyVar(x) -> (x, floatType())::tySubs
                          | _ -> tySubs
                          end
         | boolType() -> case typeSubst(ty2, tySubs) of
                         | tyVar(x) -> (x, boolType())::tySubs
                         | _ -> tySubs
                         end
         | charType() -> case typeSubst(ty2, tySubs) of
                         | tyVar(x) -> (x, charType())::tySubs
                         | _ -> tySubs
                         end
         | stringType() -> case typeSubst(ty2, tySubs) of
                           | tyVar(x) -> (x, stringType())::tySubs
                           | _ -> tySubs
                           end
         | exceptionType() -> case typeSubst(ty2, tySubs) of
                              | tyVar(x) -> (x, exceptionType())::tySubs
                              | _ -> tySubs
                              end
         | unitType() -> case typeSubst(ty2, tySubs) of
                         | tyVar(x) -> (x, unitType())::tySubs
                         | _ -> tySubs
                         end
         | arrowType(a1, a2) ->
           case typeSubst(ty2, tySubs) of
           | tyVar(x) -> (x, arrowType(a1, a2))::tySubs
           | arrowType(b1, b2) ->
             typeUnify(a2, b2, typeUnify(a1, b1, tySubs))
           | _ -> tySubs
           end
         | tyVar(v) -> case typeSubst(ty2, tySubs) of
                       | tyVar(x) -> if x == v
                                     then tySubs
                                     else (v, tyVar(x))::tySubs
                       | t -> (v, t)::tySubs
                       end
         | parameterizedTyConstructor(l1, name1) ->
           case typeSubst(ty2, tySubs) of
           | tyVar(x) ->
             (x, parameterizedTyConstructor(l1, name1))::tySubs
           | parameterizedTyConstructor(l2, name2)
             when name1 == name2 -> typeListUnify(l1, l2, tySubs)
           | _ -> tySubs
           end
         | tupleType(c1) -> case typeSubst(ty2, tySubs) of
                            | tyVar(x) -> (x, tupleType(c1))::tySubs
                            | tupleType(c2) ->
                              tupleTyBuildUnify(c1, c2, tySubs)
                            | _ -> tySubs
                            end
         end;
}
function tupleTyBuildUnify
[(String, Type)] ::= ttb1::TupleTyBuild ttb2::TupleTyBuild tySubs::[(String, Type)]
{
  return case ttb1, ttb2 of
         | tupleTyBuildAdd(t1, r1), tupleTyBuildAdd(t2, r2) ->
           tupleTyBuildUnify(r1, r2, typeUnify(t1, t2, tySubs))
         | _, _ -> tySubs
         end;
}
function typeListUnify
[(String, Type)] ::= l1::[Type] l2::[Type] tySubs::[(String, Type)]
{
  return case l1, l2 of
         | h1::t1, h2::t2 ->
           typeListUnify(t1, t2, typeUnify(h1, h2, tySubs))
         | _, _ -> tySubs
         end;
}

function typeListUnify_ByName
[(String, Type)] ::= l1::[(String, Type)] l2::[(String, Type)] tySubs::[(String, Type)]
{
  return case l1 of
         | [] -> tySubs
         | (n, t)::tl ->
           case lookupName(n, l2) of
           | just(ty) -> 
             typeListUnify_ByName(tl, l2, typeUnify(t, ty, tySubs))
           | nothing() -> tySubs
           end
         end;
}


--make all possible substitutions to get the most-specific type
function typeSubst
Type ::= ty::Type tySubs::[(String, Type)]
{
  return case ty of
         | intType() -> intType()
         | floatType() -> floatType()
         | boolType() -> boolType()
         | charType() -> charType()
         | stringType() -> stringType()
         | exceptionType() -> exceptionType()
         | unitType() -> unitType()
         | arrowType(ty1, ty2) ->
           arrowType(typeSubst(ty1, tySubs), typeSubst(ty2, tySubs))
         | tyVar(v) -> case lookupName(v, tySubs) of
                       | just(ty) -> typeSubst(ty, tySubs)
                       | nothing() -> tyVar(v)
                       end
         | parameterizedTyConstructor(l, name) ->
           parameterizedTyConstructor(typeSubst_List(l, tySubs), name)
         | tupleType(contents) ->
           tupleType(typeSubst_TupleTyBuild(contents, tySubs))
         end;
}
function typeSubst_TupleTyBuild
TupleTyBuild ::= ttb::TupleTyBuild tySubs::[(String, Type)]
{
  return case ttb of
         | tupleTyBuildAdd(ty, rest) ->
           tupleTyBuildAdd(typeSubst(ty, tySubs),
                           typeSubst_TupleTyBuild(rest, tySubs))
         | tupleTyBuildEnd() -> tupleTyBuildEnd()
         end;
}
function typeSubst_List
[Type] ::= l::[Type] tySubs::[(String, Type)]
{
  return case l of
         | [] -> []
         | ty::tl -> typeSubst(ty, tySubs)::typeSubst_List(tl, tySubs)
         end;
}

function typeSubst_ListNamesTys
[(String, Type)] ::= l::[(String, Type)] tySubs::[(String, Type)]
{
  return case l of
         | [] -> []
         | (n, ty)::tl ->
           (n, typeSubst(ty, tySubs))::typeSubst_ListNamesTys(tl, tySubs)
         end;
}


--check whether two types are equal under the given substitution
function typeEqual
Boolean ::= ty1::Type ty2::Type tySubs::[(String, Type)]
{
  return typeEqual_helper(typeSubst(ty1, tySubs),
                          typeSubst(ty2, tySubs));
}
function typeEqual_helper
Boolean ::= ty1::Type ty2::Type
{
  return case ty1, ty2 of
         | intType(), intType() -> true
         | floatType(), floatType() -> true
         | boolType(), boolType() -> true
         | charType(), charType() -> true
         | stringType(), stringType() -> true
         | exceptionType(), exceptionType() -> true
         | unitType(), unitType() -> true
         | arrowType(a1, a2), arrowType(b1, b2) ->
           typeEqual_helper(a1, b1) && typeEqual_helper(a2, b2)
         | tyVar(v1), tyVar(v2) -> v1 == v2
         | parameterizedTyConstructor(l1, name1),
           parameterizedTyConstructor(l2, name2) ->
           typeEqual_TypeList_helper(l1, l2) && name1 == name2
         | tupleType(contents1), tupleType(contents2) ->
           typeEqual_TupleTyBuild(contents1, contents2)
         | _, _ -> false
         end;
}
function typeEqual_TupleTyBuild
Boolean ::= ttb1::TupleTyBuild ttb2::TupleTyBuild
{
  return case ttb1, ttb2 of
         | tupleTyBuildAdd(t1, r1), tupleTyBuildAdd(t2, r2) ->
           typeEqual_helper(t1, t2) && typeEqual_TupleTyBuild(r1, r2)
         | tupleTyBuildEnd(), tupleTyBuildEnd() -> true
         | _, _ -> false
         end;
}
function typeEqual_TypeList_helper
Boolean ::= l1::[Type] l2::[Type]
{
  return case l1, l2 of
         | [], [] -> true
         | h1::t1, h2::t2 ->
           typeEqual_helper(h1, h2) && typeEqual_TypeList_helper(t1, t2)
         | _, _ -> false
         end;
}

function typeEqual_TypeList
Boolean ::= l1::[Type] l2::[Type] subs::[(String, Type)]
{
  return typeEqual_TypeList_helper(typeSubst_List(l1, subs), typeSubst_List(l2, subs));
}

--all names in both are related (no extra names in either one)
function typeEqual_TypeList_ByName
Boolean ::= l1::[(String, Type)] l2::[(String, Type)] tySubs::[(String, Type)]
{
  local substl1::[(String, Type)] = typeSubst_ListNamesTys(l1, tySubs);
  local substl2::[(String, Type)] = typeSubst_ListNamesTys(l2, tySubs);
  return typeEqual_TypeList_ByName_helper(substl1, substl2) &&
         typeEqual_TypeList_ByName_helper(substl2, substl1);
}
function typeEqual_TypeList_ByName_helper
Boolean ::= l1::[(String, Type)] l2::[(String, Type)]
{
  --everything in l1 is equal to the same name in l2
  return case l1 of
         | [] -> true
         | (n,t)::tl ->
           case lookupName(n, l2) of
           | just(t2) ->
             typeEqual_helper(t, t2) &&
             typeEqual_TypeList_ByName_helper(tl, l2)
           | nothing() -> false
           end
         end;
}


--Get a fresh variable type to use for unknown types
function freshType
Type ::=
{
  return tyVar("__ty_var_" ++ toString(genInt()));
}
function freshListType
Type ::=
{
  return parameterizedTyConstructor([freshType()], "list");
}


{-We want to generate new types so that we can use a constructor or a
  function at different types in the same expression, or in case we
  happen to have the same type variable in unrelated functions or
  constructors.

  We can simply map over fv to create the new substition even though
  it might contain duplicates because, even if we have multiple fresh
  types for the same name, only one fresh type will be substituted
  in.-}
function typeFreshen
Type ::= ty::Type subs::[(String, Type)]
{
  local aty::Type = typeSubst(ty, subs);
  local fv::[String] = aty.freeTyVars;
  local newsubs::[(String, Type)] = map(\x::String -> (x, freshType()), fv);
  return typeSubst(aty, newsubs);
}




--build an arrow type from a result and a list of premises
function buildArrowType
Type ::= l::[Type] result::Type
{
  return case l of
         | [] -> result
         | h::t -> arrowType(h, buildArrowType(t, result))
         end;
}



--types known before the current definition set
--this is for determining whether a type has been defined before
restricted inherited attribute priorTypes::[(String, ExtantType)];
--The name of the type being defined
restricted synthesized attribute name::String;

restricted inherited attribute knownTyVars::[String];

nonterminal TypeDef with
   pp, knownTypes, knownTypes_out, knownConstructors, knownConstructors_out, defOK, priorTypes, name;

abstract production inductiveTypeDef
top::TypeDef ::= params::TypeParams name::String constructors::Constructors
{
  top.pp = "(" ++ params.pp ++ ") " ++ name ++ " = " ++ constructors.pp;

  --we need to add the type parameters to check for it being a valid definition
  restricted constructors.knownTypes = top.knownTypes;
  restricted top.knownTypes_out = [(name, inductiveExtant(params.len))];

  restricted constructors.knownTyVars = params.names;

  restricted constructors.knownConstructors = top.knownConstructors;
  restricted top.knownConstructors_out = constructors.knownConstructors_out;

  restricted constructors.buildingType = parameterizedTyConstructor(params.tyParams, name);

  restricted top.name = name;

  restricted top.defOK = case lookupType(name, top.priorTypes) of
                       | just(_) -> false
                       | nothing() -> constructors.defOK
                       end;
}


restricted synthesized attribute len::Integer;
restricted synthesized attribute tyParams::[Type];
restricted synthesized attribute names::[String];

nonterminal TypeParams with pp, len, tyParams, names;

abstract production typeParamsAdd
top::TypeParams ::= name::String rest::TypeParams
{
  top.pp = "'" ++ name ++ ", " ++ rest.pp;

  restricted top.len = rest.len + 1;

  restricted top.tyParams = tyVar(name)::rest.tyParams;

  restricted top.names = name::rest.names;
}

abstract production typeParamsEnd
top::TypeParams ::=
{
  top.pp = "";

  restricted top.len = 0;

  restricted top.tyParams = [];

  restricted top.names = [];
}


--The type the constructors are going to be building.
restricted inherited attribute buildingType::Type;

nonterminal Constructors with
   pp, buildingType, gamma, knownTypes, knownTyVars, knownConstructors, knownConstructors_out, defOK;
nonterminal Constructor with
   pp, buildingType, gamma, knownTypes, knownTyVars, knownConstructors, knownConstructors_out, defOK;

abstract production constructorNoParams
top::Constructor ::= name::String
{
  top.pp = name;

  restricted top.knownConstructors_out = [(name, top.buildingType)];

  restricted top.defOK = case lookupName(name, top.knownConstructors) of
                       | just(_) -> false
                       | nothing() -> true
                       end;
}


abstract production constructorParams
top::Constructor ::= name::String ty::Type
{
  top.pp = name ++ " of (" ++ ty.pp ++ ")";

  restricted ty.knownTypes = top.knownTypes;

  restricted ty.knownTyVars = top.knownTyVars;

  restricted top.knownConstructors_out = [(name, arrowType(ty, top.buildingType))];

  restricted top.defOK = case lookupName(name, top.knownConstructors) of
                       | just(_) -> false
                       | nothing() -> ty.validType
                       end;
}


abstract production constructorsAdd
top::Constructors ::= c::Constructor rest::Constructors
{
  top.pp = c.pp ++ " | " ++ rest.pp;

  restricted c.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = c.knownConstructors_out ++ top.knownConstructors;
  restricted top.knownConstructors_out = c.knownConstructors_out ++ rest.knownConstructors_out;

  restricted c.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted c.knownTyVars = top.knownTyVars;
  restricted rest.knownTyVars = top.knownTyVars;

  restricted c.buildingType = top.buildingType;
  restricted rest.buildingType = top.buildingType;

  restricted top.defOK = c.defOK && rest.defOK;
}


abstract production constructorsEnd
top::Constructors ::=
{
  top.pp = "";

  restricted top.knownConstructors_out = [];

  restricted top.defOK = true;
}


nonterminal Labels with pp;
nonterminal Label with pp;

abstract production labelsAdd
top::Labels ::= l::Label rest::Labels
{
  top.pp = l.pp ++ "; " ++ rest.pp;
}


abstract production labelsEnd
top::Labels ::=
{
  top.pp = "";
}


abstract production labelImmutable
top::Label ::= name::String ty::Type
{
  top.pp = name ++ " : " ++ ty.pp;
}


abstract production labelMutable
top::Label ::= name::String ty::Type
{
  top.pp = "mutable " ++ name ++ " : " ++ ty.pp;
}


abstract production aliasTypeDef
top::TypeDef ::= params::TypeParams name::String ty::Type
{
  top.pp = "(" ++ params.pp ++ ") " ++ name ++ " == " ++ ty.pp;

  restricted top.knownTypes_out = error("knownTypes_out for aliasTypeDef");

  restricted top.knownConstructors_out = error("knownConstructors_out for aliasTypeDef");

  restricted top.name = name;

  restricted top.defOK = error("defOK for aliasTypeDef");
}


abstract production undefinedTypeDef
top::TypeDef ::= params::TypeParams name::String
{
  top.pp = "(" ++ params.pp ++ ") " ++ name;

  restricted top.knownTypes_out = error("knownTypes_out for undefinedTypeDef");

  restricted top.knownConstructors_out = error("knownConstructors_out for undefinedTypeDef");

  restricted top.name = name;

  restricted top.defOK = error("defOK for undefinedTypeDef");
}



nonterminal TypeDefs with
   pp, knownTypes_out, knownTypes, knownConstructors, knownConstructors_out, defOK, priorTypes, tyNames;

abstract production typeDefsAdd
top::TypeDefs ::= td::TypeDef rest::TypeDefs
{
  top.pp = td.pp ++ " and " ++ rest.pp;

  restricted td.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted top.knownTypes_out = td.knownTypes_out ++ rest.knownTypes_out;

  restricted td.priorTypes = top.priorTypes;
  restricted rest.priorTypes = top.priorTypes;

  restricted td.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = td.knownConstructors_out ++ top.knownConstructors;
  restricted top.knownConstructors_out = td.knownConstructors_out ++ rest.knownConstructors_out;

  restricted top.defOK = td.defOK && rest.defOK &&
                       --check that the current typedef is not in the rest of the definitions
                       case lookupType(td.name, rest.knownTypes_out) of
                       | just(_) -> false
                       | nothing() -> true
                       end;

  restricted top.tyNames = td.name::rest.tyNames;
}


abstract production typeDefsEnd
top::TypeDefs ::=
{
  top.pp = "";

  restricted top.knownTypes_out = [];

  restricted top.knownConstructors_out = [];

  restricted top.defOK = true;

  restricted top.tyNames = [];
}


restricted synthesized attribute tyNames::[String];

nonterminal TypeDefinition with
   pp, knownTypes, knownTypes_out, knownConstructors, knownConstructors_out, defOK, tyNames;

abstract production tyDefinition
top::TypeDefinition ::= tydefs::TypeDefs
{
  top.pp = tydefs.pp;

  restricted tydefs.knownTypes = tydefs.knownTypes_out ++ top.knownTypes;
  restricted top.knownTypes_out = tydefs.knownTypes_out;

  restricted tydefs.priorTypes = top.knownTypes;

  restricted tydefs.knownConstructors = top.knownConstructors;
  restricted top.knownConstructors_out = tydefs.knownConstructors_out;

  restricted top.defOK = tydefs.defOK;

  restricted top.tyNames = tydefs.tyNames;
}





{-This is to keep track of types that have been declared.-}
nonterminal ExtantType;

abstract production inductiveExtant
top::ExtantType ::= argNums::Integer
{

}


abstract production equalExtant
top::ExtantType ::= ty::Type
{

}


abstract production undefinedExtant
top::ExtantType ::=
{

}


function knownTypes_ToString
String ::= l::[(String, ExtantType)]
{
  return case l of
         | [] -> ""
         | (name, inductiveExtant(num))::tl ->
           name ++ " : Inductive type with " ++ toString(num) ++ " parametetrs; " ++ knownTypes_ToString(tl)
         | (name, equalExtant(t))::tl ->
           name ++ " : Equal to " ++ t.pp ++ "; " ++ knownTypes_ToString(tl)
         | (name, undefinedExtant())::tl ->
           name ++ " : Undefined type; " ++ knownTypes_ToString(tl)
         end;
}


function ctx_ToString
String ::= l::[(String, Type)]
{
  return case l of
         | [] -> ""
         | (name, ty)::tl ->
           name ++ " : " ++ ty.pp ++ ";\n" ++ ctx_ToString(tl)
         end;
}


--Make it so we can print out a type a lot nicer by putting in nicer variable names
--If there are more than 26 free variables, it doesn't matter what their names are,
--   it is going to be confusing, so it doesn't matter if we start putting out less
--   nice variable names at that point
function typePrettify
Type ::= ty::Type
{
  local niceVars::[String] =
           ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
            "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"];
  local fv::[String] = ty.freeTyVars;
  local fvClean::[String] = removeDuplicates(fv);
  local temp::([String], [String]) = intersectionComplement(fvClean, niceVars);
  local goodNiceVars::[String] = snd(temp);
  local goodFV::[String] = fst(temp);
  local subs::[(String, Type)] = makeSubs(goodFV, goodNiceVars);
  return typeSubst(ty, subs);
}

function removeDuplicates
[String] ::= l::[String]
{
  return case l of
         | [] -> []
         | h::t -> h::removeDuplicates(removeOccurrences(t, h))
         end;
}

function removeOccurrences
[String] ::= l::[String] s::String
{
  return case l of
         | [] -> []
         | h::t -> if h == s
                   then removeOccurrences(t, s)
                   else h::removeOccurrences(t, s)
         end;
}

--remove anything that occurs in both from both
--assume elements in l1 are unique
function intersectionComplement
([String], [String]) ::= l1::[String] l2::[String]
{
  return case l1 of
         | [] -> ([], l2)
         | h::t ->
           if containsBy(\x::String y::String -> x == y, h, l2)
           then intersectionComplement(t, removeOccurrences(l2, h))
           else case intersectionComplement(t, l2) of
                | (r1, r2) -> (h::r1, r2)
                end
         end;
}

function makeSubs
[(String, Type)] ::= original::[String] newnames::[String]
{
  return case original, newnames of
         | [], _ -> []
         | _, [] -> []
         | h1::t1, h2::t2 -> (h1, tyVar(h2))::makeSubs(t1, t2)
         end;
}

