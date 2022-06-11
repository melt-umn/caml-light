grammar grammars:abstractSyntax;


function noRepeatedNames
Boolean ::= l1::[Pair<String Type>] l2::[Pair<String Type>]
{
  return noRepeatedNames_helper(l1, l2) &&
         noRepeatedNames_helper(l2, l1);
}
function noRepeatedNames_helper
Boolean ::= l1::[Pair<String Type>] l2::[Pair<String Type>]
{
  --no name from l1 in l2
  return case l1 of
         | [] -> true
         | pair(hn, ht)::t -> case lookupName(hn, l2) of
                              | just(_) -> false
                              | nothing() -> noRepeatedNames_helper(t, l2)
                              end
         end;
}


--no shared names between the lists
function namesDisjoint
Boolean ::= l1::[Pair<String Type>] l2::[Pair<String Type>]
{
  return case l1 of
  | [] -> true
  | pair(n,ty)::tl -> case lookupName(n, l2) of
                      | nothing() -> namesDisjoint(tl, l2)
                      | just(_) -> false
                      end
  end;
}


nonterminal Pattern with
   pp, subst, subst_out, type, gamma_out, knownConstructors, knownTypes;

abstract production intPattern
top::Pattern ::= i::Integer
{
  top.pp = toString(i);

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = intType();
}


abstract production floatPattern
top::Pattern ::= f::Float
{
  top.pp = toString(f);

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = floatType();
}


abstract production charPattern
top::Pattern ::= c::String
{
  top.pp = "'" ++ c ++ "'";

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = charType();
}


abstract production stringPattern
top::Pattern ::= s::String
{
  top.pp = "\"" ++ s ++ "\"";

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = stringType();
}


abstract production unitPattern
top::Pattern ::=
{
  top.pp = "()";

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = unitType();
}


abstract production defaultPattern
top::Pattern ::=
{
  top.pp = "_"; 

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = freshType();
}


abstract production optionPattern
top::Pattern ::= p1::Pattern p2::Pattern
{
  top.pp = "(" ++ p1.pp ++ ") | (" ++ p2.pp ++ ")";

  restricted p1.knownTypes = top.knownTypes;
  restricted p2.knownTypes = top.knownTypes;

  restricted p1.knownConstructors = top.knownConstructors;
  restricted p2.knownConstructors = top.knownConstructors;

  --p1.gamma_out and p2.gamma_out should have the same bindings
  implicit top.gamma_out = p1.gamma_out;

  implicit p1.subst = top.subst;
  implicit p2.subst = p1.subst_out;
  implicit top.subst_out = typeListUnify_ByName(p1.gamma_out, p2.gamma_out,
                                                typeUnify(p1.type, p2.type, p2.subst_out));

  implicit top.type = if typeEqual(p1.type, p2.type, top.subst_out) &&
                         typeEqual_TypeList_ByName(p1.gamma_out, p2.gamma_out, top.subst_out)
                      then p1.type
                      end;
}


abstract production consPattern
top::Pattern ::= p1::Pattern p2::Pattern
{
  top.pp = "(" ++ p1.pp ++ ")::(" ++ p2.pp ++ ")";

  restricted p1.knownTypes = top.knownTypes;
  restricted p2.knownTypes = top.knownTypes;

  restricted p1.knownConstructors = top.knownConstructors;
  restricted p2.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = p1.gamma_out ++ p2.gamma_out;

  implicit p1.subst = top.subst;
  implicit p2.subst = p1.subst_out;
  implicit top.subst_out = typeUnify(parameterizedTyConstructor([p1.type], "list"),
                                     p2.type, p2.subst_out);

  implicit top.type = case typeSubst(p2.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "list")
                        when typeEqual(a, p1.type, top.subst_out) &&
                             --check no names are bound twice
                             noRepeatedNames(p1.gamma_out, p2.gamma_out) -> p2.type
                      end;
}


abstract production listPattern
top::Pattern ::= contents::ListPatternContents
{
  top.pp = "[" ++ contents.pp ++ "]";

  restricted contents.knownTypes = top.knownTypes;

  restricted contents.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = contents.gamma_out;

  implicit contents.subst = top.subst;
  implicit top.subst_out = contents.subst_out;

  implicit top.type = parameterizedTyConstructor([contents.type], "list");
}


nonterminal ListPatternContents with
   pp, gamma_out, subst, subst_out, type, knownConstructors, knownTypes;

abstract production listPatternContentsAdd
top::ListPatternContents ::= p::Pattern rest::ListPatternContents
{
  top.pp = p.pp ++ "; " ++ rest.pp;

  restricted p.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = p.gamma_out ++ rest.gamma_out;

  implicit p.subst = top.subst;
  implicit rest.subst = p.subst_out;
  implicit top.subst_out = typeUnify(p.type, rest.type, rest.subst_out);

  implicit top.type = if typeEqual(p.type, rest.type, top.subst_out) &&
                         --unique names bound in different parts
                         namesDisjoint(p.gamma_out, rest.gamma_out)
                      then p.type
                      end;
}


abstract production listPatternContentsEnd
top::ListPatternContents ::=
{
  top.pp = "";

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.type = freshType();
}


abstract production namedPattern
top::Pattern ::= p::Pattern name::String
{
  top.pp = "(" ++ p.pp ++ ") as " ++ name;

  restricted p.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = pair(name, p.type)::p.gamma_out;

  implicit p.subst = top.subst;
  implicit top.subst_out = p.subst_out;

  --the name being bound here cannot be bound elsewhere
  implicit top.type = if namesDisjoint([pair(name, p.type)], p.gamma_out)
                      then p.type
                      end;
}


abstract production ascriptionPattern
top::Pattern ::= p::Pattern ty::Type
{
  top.pp = "(" ++ p.pp ++ " : " ++ ty.pp ++ ")";

  restricted p.knownTypes = top.knownTypes;
  restricted ty.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = p.gamma_out;

  implicit p.subst = top.subst;
  implicit top.subst_out = typeUnify(p.type, ty, p.subst_out);

  implicit top.type = if typeEqual(p.type, ty, top.subst_out) && ty.validNewVarType
                      then ty
                      end;
}


abstract production constructorPattern
top::Pattern ::= name::String children::Pattern
{
  top.pp = name ++ "(" ++ children.pp ++ ")";

  restricted children.knownTypes = top.knownTypes;

  restricted children.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = children.gamma_out;

  implicit children.subst = top.subst;
  implicit top.subst_out = typeUnify(arrowType(children.type, freshType()),
                                     lookupName(name, top.knownConstructors), children.subst_out);

  implicit top.type = case typeSubst(lookupName(name, top.knownConstructors), top.subst_out) of
                      | arrowType(ty1, ty2) when typeEqual(ty1, children.type, top.subst_out) -> ty2
                      end;
}


--This may be a variable, or it may be a constructor with no arguments
abstract production simpleNamePattern
top::Pattern ::= name::String
{
  top.pp = name;

  --if it isn't a constructor, it's a variable, so bind it and put it out
  --unitType() is a placeholder for making the Silver type correct but is ignored
  implicit top.gamma_out = if containsBy(\p1::Pair<String Type> p2::Pair<String Type> ->
                                            fst(p1) == fst(p2),
                                         pair(name, unitType()), top.knownConstructors)
                           then []
                           else [pair(name, freshType())];

  implicit top.subst_out = top.subst;

  implicit top.type = if null(top.gamma_out)
                      then lookupName(name, top.knownConstructors)
                      else snd(head(top.gamma_out));
}


abstract production tuplePattern
top::Pattern ::= contents::TuplePatternContents
{
  top.pp = "(" ++ contents.pp ++ ")";

  restricted contents.knownTypes = top.knownTypes;

  restricted contents.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = contents.gamma_out;

  implicit contents.subst = top.subst;
  implicit top.subst_out = contents.subst_out;

  implicit top.type = tupleType(contents.ttb_type);
}


implicit synthesized attribute ttb_type::Maybe<TupleTyBuild>;

nonterminal TuplePatternContents with
   pp, gamma, gamma_out, subst, subst_out, ttb_type, knownConstructors, knownTypes;

abstract production tuplePatternContentsAdd
top::TuplePatternContents ::= p::Pattern rest::TuplePatternContents
{
  top.pp = p.pp ++ ", " ++ rest.pp;

  restricted p.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit p.subst = top.subst;
  implicit rest.subst = p.subst_out;
  implicit top.subst_out = rest.subst_out;

  implicit top.gamma_out = p.gamma_out ++ rest.gamma_out;

  implicit top.ttb_type = if --unique names bound in different parts
                             namesDisjoint(p.gamma_out, rest.gamma_out)
                          then tupleTyBuildAdd(p.type, rest.ttb_type)
                          end;
}


abstract production tuplePatternContentsEnd
top::TuplePatternContents ::=
{
  top.pp = "";

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.ttb_type = tupleTyBuildEnd();
}



