grammar edu:umn:cs:melt:camlLight:abstractSyntax;


synthesized attribute pp::String;

implicit synthesized attribute type::Maybe<Type>;


nonterminal Expr with
   pp, type, gamma, subst, subst_out, knownConstructors, knownTypes;


abstract production letExpr
top::Expr ::= b::Bindings e::Expr
{
  top.pp = "let " ++ b.pp ++ " in " ++ e.pp;

  restricted b.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;

  restricted b.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;

  implicit b.gamma = top.gamma;
  implicit e.gamma = b.gamma_out ++ top.gamma;

  implicit b.subst = top.subst;
  implicit e.subst = b.subst_out;
  implicit top.subst_out = e.subst_out;

  implicit top.type = if b.typeOK
                      then e.type
                      end;
}


--To make sure bindings are well-typed, where we don't get a type out, we need a Boolean
implicit synthesized attribute typeOK::Maybe<Boolean>;

nonterminal Bindings with
   pp, gamma, gamma_out, subst, subst_out, knownConstructors, typeOK, knownTypes;

abstract production bindingsAdd
top::Bindings ::= p::Pattern e::Expr rest::Bindings
{
  top.pp = "(" ++ p.pp ++ ") = " ++ e.pp ++ " and " ++ rest.pp;

  restricted p.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;
  implicit rest.gamma = top.gamma;
  implicit top.gamma_out = rest.gamma_out ++ p.gamma_out;

  implicit p.subst = top.subst;
  implicit e.subst = p.subst_out;
  implicit rest.subst = e.subst_out;

  implicit top.subst_out = typeUnify(p.type, e.type, rest.subst_out);

  implicit top.typeOK = typeEqual(p.type, e.type, top.subst_out) && rest.typeOK;
}


abstract production bindingsEnd
top::Bindings ::=
{
  top.pp = "";

  implicit top.gamma_out = [];
  implicit top.subst_out = top.subst;
  implicit top.typeOK = true;
}


abstract production letRecExpr
top::Expr ::= b::RecBindings e::Expr
{
  top.pp = "let rec " ++ b.pp ++ " in " ++ e.pp;

  restricted b.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;

  restricted b.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;

  implicit b.gamma = b.gamma_out ++ top.gamma;
  implicit e.gamma = b.gamma_out ++ top.gamma;

  implicit b.recSubst = top.subst;
  implicit b.subst = b.recSubst_out;
  implicit e.subst = b.subst_out;
  implicit top.subst_out = e.subst_out;

  implicit top.type = if b.typeOK
                      then e.type
                      end;
}


--we need rec substs so gamma_out doesn't depend on the regular subst, which depends on e.type
implicit inherited attribute recSubst::Maybe<[(String, Type)]>;
implicit synthesized attribute recSubst_out::Maybe<[(String, Type)]>;

nonterminal RecBindings with
   pp, gamma, gamma_out, subst, subst_out, knownConstructors, typeOK, knownTypes, recSubst, recSubst_out;

abstract production recBindingsAdd
top::RecBindings ::= p::Pattern e::Expr rest::RecBindings
{
  top.pp = "(" ++ p.pp ++ ") = " ++ e.pp ++ " and " ++ rest.pp;

  restricted p.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit p.subst = top.recSubst;
  implicit rest.recSubst = p.subst_out;
  implicit top.recSubst_out = rest.recSubst_out;

  implicit top.gamma_out = rest.gamma_out ++ p.gamma_out;

  implicit e.gamma = top.gamma;
  implicit rest.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit rest.subst = e.subst_out;
  implicit top.subst_out = typeUnify(p.type, e.type, rest.subst_out);

  implicit top.typeOK = typeEqual(p.type, e.type, top.subst_out) && rest.typeOK;
}


abstract production recBindingsEnd
top::RecBindings ::=
{
  top.pp = "";

  implicit top.recSubst_out = top.recSubst;
  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;
  implicit top.typeOK = true;
}


abstract production exprSeq
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ "); " ++ e2.pp;

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e1.type, unitType(), e2.subst_out);

  implicit top.type = case typeSubst(e1.type, top.subst_out) of
                      | unitType() -> e2.type
                      end;
}


abstract production ifthen
top::Expr ::= c::Expr th::Expr
{
  top.pp = "if " ++ c.pp ++ " then " ++ th.pp;

  restricted c.knownTypes = top.knownTypes;
  restricted th.knownTypes = top.knownTypes;

  restricted c.knownConstructors = top.knownConstructors;
  restricted th.knownConstructors = top.knownConstructors;

  implicit c.gamma = top.gamma;
  implicit th.gamma = top.gamma;

  implicit c.subst = top.subst;
  implicit th.subst = c.subst_out;
  implicit top.subst_out = typeUnify(th.type, unitType(),
                                     typeUnify(c.type, boolType(), th.subst_out));

  implicit top.type = case typeSubst(c.type, top.subst_out), typeSubst(th.type, top.subst_out) of
                      | boolType(), unitType() -> unitType()
                      end;
}


abstract production ifthenelse
top::Expr ::= c::Expr th::Expr el::Expr
{
  top.pp = "if " ++ c.pp ++ " then (" ++ th.pp ++ ") else " ++ el.pp;

  restricted c.knownTypes = top.knownTypes;
  restricted th.knownTypes = top.knownTypes;
  restricted el.knownTypes = top.knownTypes;

  restricted c.knownConstructors = top.knownConstructors;
  restricted th.knownConstructors = top.knownConstructors;
  restricted el.knownConstructors = top.knownConstructors;

  implicit c.gamma = top.gamma;
  implicit th.gamma = top.gamma;
  implicit el.gamma = top.gamma;

  implicit c.subst = top.subst;
  implicit th.subst = c.subst_out;
  implicit el.subst = th.subst_out;
  implicit top.subst_out = typeUnify(th.type, el.type,
                                     typeUnify(c.type, boolType(), el.subst_out));

  implicit top.type = case typeSubst(c.type, top.subst_out) of
                      | boolType() when typeEqual(th.type, el.type, top.subst_out) -> th.type
                      end;
}


abstract production refAssign
top::Expr ::= loc::Expr value::Expr
{
  top.pp = "(" ++ loc.pp ++ ") := (" ++ value.pp ++ ")";

  restricted loc.knownTypes = top.knownTypes;
  restricted value.knownTypes = top.knownTypes;

  restricted loc.knownConstructors = top.knownConstructors;
  restricted value.knownConstructors = top.knownConstructors;

  implicit loc.gamma = top.gamma;
  implicit value.gamma = top.gamma;

  implicit loc.subst = top.subst;
  implicit value.subst = loc.subst_out;
  implicit top.subst_out = typeUnify(parameterizedTyConstructor([value.type], "reference"),
                                     loc.type, value.subst_out);

  implicit top.type = case typeSubst(loc.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "reference")
                        when typeEqual(a, value.type, top.subst_out) -> unitType()
                      end;
}


abstract production tuple
top::Expr ::= tc::TupleContents
{
  top.pp = "(" ++ tc.pp ++ ")";

  restricted tc.knownTypes = top.knownTypes;

  restricted tc.knownConstructors = top.knownConstructors;

  implicit tc.gamma = top.gamma;

  implicit tc.subst = top.subst;
  implicit top.subst_out = tc.subst_out;

  implicit top.type = tupleType(tc.tc_type);
}


implicit synthesized attribute tc_type::Maybe<TupleTyBuild>;


nonterminal TupleContents with
   pp, gamma, subst, subst_out, tc_type, knownConstructors, knownTypes;

abstract production tupleContentsAdd
top::TupleContents ::= e1::Expr rest::TupleContents
{
  top.pp = e1.pp ++ ", " ++ rest.pp;

  restricted e1.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit rest.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit rest.subst = e1.subst_out;
  implicit top.subst_out = rest.subst_out;

  implicit top.tc_type = tupleTyBuildAdd(e1.type, rest.tc_type);
}


abstract production tupleContentsEnd
top::TupleContents ::=
{
  top.pp = "";

  implicit top.subst_out = top.subst;

  implicit top.tc_type = tupleTyBuildEnd();
}


abstract production var
top::Expr ::= name::String
{
  top.pp = name;

  implicit top.subst_out = top.subst;

  --we need to freshen anything with an arrow type or constructors without an arrow type
  --We also need to ban binding names of known constructors, which means gamma will not contain
  --   any of the same names as the constructors, so the name being looked up can only be found in one, not both
  implicit top.type = if containsBy(\p1::(String, Type) p2::(String, Type) -> fst(p1) == fst(p2),
                                    (name, unitType()), top.knownConstructors)  --unit is an unused placeholder
                      then typeFreshen(lookupName(name, top.knownConstructors), top.subst_out)
                      else case typeSubst(lookupName(name, top.gamma), top.subst_out) of
                           | arrowType(ty1, ty2) -> typeFreshen(arrowType(^ty1, ^ty2), top.subst_out)
                           | ty -> ty
                           end;
}


abstract production intConst
top::Expr ::= i::Integer
{
  top.pp = toString(i);

  implicit top.subst_out = top.subst;
  implicit top.type = intType();
}


abstract production floatConst
top::Expr ::= f::Float
{
  top.pp = toString(f);

  implicit top.subst_out = top.subst;
  implicit top.type = floatType();
}


abstract production charConst
top::Expr ::= c::String
{
  top.pp = "'" ++ c ++ "'";

  implicit top.subst_out = top.subst;
  implicit top.type = charType();
}


abstract production stringConst
top::Expr ::= contents::String
{
  top.pp = "\"" ++ contents ++ "\"";

  implicit top.subst_out = top.subst;
  implicit top.type = stringType();
}


abstract production unitExpr
top::Expr ::=
{
  top.pp = "()";

  implicit top.subst_out = top.subst;
  implicit top.type = unitType();
}


abstract production emptyListExpr
top::Expr ::=
{
  top.pp = "[]";

  implicit top.subst_out = top.subst;

  implicit top.type = freshListType();
}


abstract production app
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e1.type, arrowType(e2.type, freshType()), e2.subst_out);

  implicit top.type = case typeSubst(e1.type, top.subst_out) of
                      | arrowType(a, b) when typeEqual(^a, e2.type, top.subst_out) -> ^b
                      end;
}


abstract production while
top::Expr ::= c::Expr b::Expr
{
  top.pp = "while " ++ c.pp ++ " do " ++ b.pp ++ " done";

  restricted c.knownTypes = top.knownTypes;
  restricted b.knownTypes = top.knownTypes;

  restricted c.knownConstructors = top.knownConstructors;
  restricted b.knownConstructors = top.knownConstructors;

  implicit c.gamma = top.gamma;
  implicit b.gamma = top.gamma;

  implicit c.subst = top.subst;
  implicit b.subst = c.subst_out;
  implicit top.subst_out = typeUnify(b.type, unitType(),
                                     typeUnify(c.type, boolType(), b.subst_out));

  implicit top.type = case typeSubst(c.type, top.subst_out), typeSubst(b.type, top.subst_out) of
                      | boolType(), unitType() -> unitType()
                      end;
}


abstract production forTo
top::Expr ::= name::String startIndex::Expr endIndex::Expr body::Expr
{
  top.pp = "for " ++ name ++ " = " ++ startIndex.pp ++ " to " ++ endIndex.pp ++ " do " ++ body.pp ++ " done";

  restricted startIndex.knownTypes = top.knownTypes;
  restricted endIndex.knownTypes = top.knownTypes;
  restricted body.knownTypes = top.knownTypes;

  restricted startIndex.knownConstructors = top.knownConstructors;
  restricted endIndex.knownConstructors = top.knownConstructors;
  restricted body.knownConstructors = top.knownConstructors;

  implicit startIndex.gamma = top.gamma;
  implicit endIndex.gamma = top.gamma;
  implicit body.gamma = [(name, intType())] ++ top.gamma;

  implicit startIndex.subst = top.subst;
  implicit endIndex.subst = startIndex.subst_out;
  implicit body.subst = endIndex.subst_out;
  implicit top.subst_out = typeUnify(body.type, unitType(),
                                     typeUnify(endIndex.type, intType(),
                                     typeUnify(startIndex.type, intType(), body.subst_out)));

  implicit top.type = case typeSubst(startIndex.type, top.subst_out),
                           typeSubst(endIndex.type, top.subst_out),
                           typeSubst(body.type, top.subst_out) of
                      | intType(), intType(), unitType() -> unitType()
                      end;
}


abstract production forDownto
top::Expr ::= name::String startIndex::Expr endIndex::Expr body::Expr
{
  top.pp = "for " ++ name ++ " = " ++ startIndex.pp ++ " downto " ++ endIndex.pp ++ " do " ++ body.pp ++ " done";

  restricted startIndex.knownTypes = top.knownTypes;
  restricted endIndex.knownTypes = top.knownTypes;
  restricted body.knownTypes = top.knownTypes;

  restricted startIndex.knownConstructors = top.knownConstructors;
  restricted endIndex.knownConstructors = top.knownConstructors;
  restricted body.knownConstructors = top.knownConstructors;

  implicit startIndex.gamma = top.gamma;
  implicit endIndex.gamma = top.gamma;
  implicit body.gamma = [(name, intType())] ++ top.gamma;

  implicit startIndex.subst = top.subst;
  implicit endIndex.subst = startIndex.subst_out;
  implicit body.subst = endIndex.subst_out;
  implicit top.subst_out = typeUnify(body.type, unitType(),
                                     typeUnify(endIndex.type, intType(),
                                     typeUnify(startIndex.type, intType(), body.subst_out)));

  implicit top.type = case typeSubst(startIndex.type, top.subst_out),
                           typeSubst(endIndex.type, top.subst_out),
                           typeSubst(body.type, top.subst_out) of
                      | intType(), intType(), unitType() -> unitType()
                      end;
}


abstract production modExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") mod (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> intType()
                      end;
}


abstract production multExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") * (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> intType()
                      end;
}


abstract production multFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") *. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> floatType()
                      end;
}


abstract production divExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") / (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> intType()
                      end;
}


abstract production divFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") /. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> floatType()
                      end;
}


abstract production plusExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") + (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> intType()
                      end;
}


abstract production plusFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") +. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> floatType()
                      end;
}


abstract production minusExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") - (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> intType()
                      end;
}


abstract production minusFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") -. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> floatType()
                      end;
}


abstract production eqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") = (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e1.type, e2.type, e2.subst_out);

  implicit top.type = if typeEqual(e1.type, e2.type, top.subst_out)
                      then boolType()
                      end;
}


abstract production neqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") <> (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e1.type, e2.type, e2.subst_out);

  implicit top.type = if typeEqual(e1.type, e2.type, top.subst_out)
                      then boolType()
                      end;
}


abstract production greaterExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") > (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> boolType()
                      end;
}


abstract production greaterFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") >. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> boolType()
                      end;
}


abstract production greaterEqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") >= (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> boolType()
                      end;
}


abstract production greaterEqFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") >=. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> boolType()
                      end;
}


abstract production lessExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") < (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> boolType()
                      end;
}


abstract production lessFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") <. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));
  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> boolType()
                      end;
}


abstract production lessEqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") <= (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, intType(),
                                     typeUnify(e1.type, intType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | intType(), intType() -> boolType()
                      end;
}


abstract production lessEqFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") <=. (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> boolType()
                      end;
}


abstract production physicalEqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") == (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e1.type, e2.type, e2.subst_out);

  implicit top.type = if typeEqual(e1.type, e2.type, top.subst_out)
                      then boolType()
                      end;
}


abstract production physicalNeqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") != (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e1.type, e2.type, e2.subst_out);

  implicit top.type = if typeEqual(e1.type, e2.type, top.subst_out)
                      then boolType()
                      end;
}


abstract production andExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") & (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, boolType(),
                                     typeUnify(e1.type, boolType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | boolType(), boolType() -> boolType()
                      end;
}


abstract production orExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") or (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, boolType(),
                                     typeUnify(e1.type, boolType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | boolType(), boolType() -> boolType()
                      end;
}


abstract production expFloatExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") ** (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, floatType(),
                                     typeUnify(e1.type, floatType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | floatType(), floatType() -> floatType()
                      end;
}


abstract production listConcatenationExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") @ (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = let listTy::Type = freshListType()
                           in typeUnify(e2.type, listTy,
                                        typeUnify(e1.type, listTy, e2.subst_out))
                           end;

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "list"),
                        parameterizedTyConstructor([b], "list")
                        when typeEqual(a, b, top.subst_out) -> e1.type
                      end;
}


abstract production stringConcatenationExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ") ^ (" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(e2.type, stringType(),
                                     typeUnify(e1.type, stringType(), e2.subst_out));

  implicit top.type = case typeSubst(e1.type, top.subst_out), typeSubst(e2.type, top.subst_out) of
                      | stringType(), stringType() -> e1.type
                      end;
}


abstract production notExpr
top::Expr ::= e::Expr
{
  top.pp = "not (" ++ e.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit top.subst_out = typeUnify(e.type, boolType(), e.subst_out);

  implicit top.type = case e.type of
                      | boolType() -> boolType()
                      end;
}


abstract production negExpr
top::Expr ::= e::Expr
{
  top.pp = "- (" ++ e.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit top.subst_out = typeUnify(e.type, intType(), e.subst_out);

  implicit top.type = case e.type of
                      | intType() -> intType()
                      end;
}


abstract production negFloatExpr
top::Expr ::= e::Expr
{
  top.pp = "-. (" ++ e.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit top.subst_out = typeUnify(e.type, floatType(), e.subst_out);

  implicit top.type = case e.type of
                      | floatType() -> floatType()
                      end;
}


abstract production derefExpr
top::Expr ::= e::Expr
{
  top.pp = "! (" ++ e.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit top.subst_out = typeUnify(parameterizedTyConstructor([freshType()], "reference"),
                                     e.type, e.subst_out);

  implicit top.type = case typeSubst(e.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "reference") -> a
                      end;
}


abstract production ascriptionExpr
top::Expr ::= e::Expr t::Type
{
  top.pp = "(" ++ e.pp ++ " : " ++ t.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;
  restricted t.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit top.subst_out = typeUnify(e.type, ^t, e.subst_out);

  implicit top.type = if typeEqual(e.type, ^t, top.subst_out) && t.validNewVarType
                      then ^t
                      end;
}


abstract production consExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = "(" ++ e1.pp ++ ")::(" ++ e2.pp ++ ")";

  restricted e1.knownTypes = top.knownTypes;
  restricted e2.knownTypes = top.knownTypes;

  restricted e1.knownConstructors = top.knownConstructors;
  restricted e2.knownConstructors = top.knownConstructors;

  implicit e1.gamma = top.gamma;
  implicit e2.gamma = top.gamma;

  implicit e1.subst = top.subst;
  implicit e2.subst = e1.subst_out;
  implicit top.subst_out = typeUnify(parameterizedTyConstructor([e1.type], "list"),
                                     e2.type, e2.subst_out);

  implicit top.type = case typeSubst(e2.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "list")
                        when typeEqual(a, e1.type, top.subst_out) -> e2.type
                      end;
}


abstract production recordExpr
top::Expr ::= contents::RecordExprContents
{
  top.pp = "{" ++ contents.pp ++ ")";

  implicit top.subst_out = error("subst_out for recordExpr");

  implicit top.type = error("type for recordExpr");
}


nonterminal RecordExprContents with pp;

abstract production recordContentsAdd
top::RecordExprContents ::= label::String e::Expr rest::RecordExprContents
{
  top.pp = label ++ " = " ++ e.pp ++ "; " ++ rest.pp;
}


abstract production recordContentsEnd
top::RecordExprContents ::=
{
  top.pp = "";
}


abstract production listExpr
top::Expr ::= contents::SemicolonSequence
{
  top.pp = "[" ++ contents.pp ++ "]";

  restricted contents.knownTypes = top.knownTypes;

  restricted contents.knownConstructors = top.knownConstructors;

  implicit contents.gamma = top.gamma;

  implicit contents.subst = top.subst;
  implicit top.subst_out = contents.subst_out;

  implicit top.type = parameterizedTyConstructor([contents.type], "list");
}


abstract production arrayExpr
top::Expr ::= contents::SemicolonSequence
{
  top.pp = "[|" ++ contents.pp ++ "|]";

  restricted contents.knownTypes = top.knownTypes;

  restricted contents.knownConstructors = top.knownConstructors;

  implicit contents.gamma = top.gamma;

  implicit contents.subst = top.subst;
  implicit top.subst_out = contents.subst_out;

  implicit top.type = parameterizedTyConstructor([contents.type], "array");
}


nonterminal SemicolonSequence with
   pp, gamma, subst, subst_out, type, knownConstructors, knownTypes;

abstract production semicolonSeqAdd
top::SemicolonSequence ::= e::Expr rest::SemicolonSequence
{
  top.pp = e.pp ++ "; " ++ rest.pp;

  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;
  implicit rest.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit rest.subst = e.subst_out;
  implicit top.subst_out = typeUnify(e.type, rest.type, rest.subst_out);

  implicit top.type = if typeEqual(e.type, rest.type, top.subst_out)
                      then e.type
                      end;
}

abstract production semicolonSeqEnd
top::SemicolonSequence ::=
{
  top.pp = "";

  implicit top.subst_out = top.subst;

  implicit top.type = freshType();
}


abstract production arrayAccessExpr
top::Expr ::= e::Expr index::Expr
{
  top.pp = "(" ++ e.pp ++ ").(" ++ index.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;
  restricted index.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;
  restricted index.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;
  implicit index.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit index.subst = e.subst_out;
  implicit top.subst_out = typeUnify(index.type, intType(),
                                     typeUnify(e.type, parameterizedTyConstructor([freshType()], "array"),
                                               index.subst_out));

  implicit top.type = case typeSubst(e.type, top.subst_out),
                           typeSubst(index.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "array"), intType() -> a
                      end;
}


abstract production arrayAssignExpr
top::Expr ::= e::Expr index::Expr value::Expr
{
  top.pp = "(" ++ e.pp ++ ").(" ++ index.pp ++ ")<-(" ++ value.pp ++ ")";

  restricted e.knownTypes = top.knownTypes;
  restricted index.knownTypes = top.knownTypes;
  restricted value.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;
  restricted index.knownConstructors = top.knownConstructors;
  restricted value.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;
  implicit index.gamma = top.gamma;
  implicit value.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit index.subst = e.subst_out;
  implicit value.subst = index.subst_out;
  implicit top.subst_out = typeUnify(index.type, intType(),
                                     typeUnify(e.type, parameterizedTyConstructor([value.type], "array"),
                                               value.subst_out));

  implicit top.type = case typeSubst(e.type, top.subst_out),
                           typeSubst(index.type, top.subst_out) of
                      | parameterizedTyConstructor([a], "array"), intType()
                        when typeEqual(a, value.type, top.subst_out) -> a
                      end;
}


abstract production functionExpr
top::Expr ::= clauses::SimpleMatching
{
  top.pp = "function " ++ clauses.pp;

  restricted clauses.knownTypes = top.knownTypes;

  restricted clauses.knownConstructors = top.knownConstructors;

  implicit clauses.gamma = top.gamma;

  implicit clauses.subst = top.subst;
  implicit top.subst_out = clauses.subst_out;

  implicit top.type = arrowType(clauses.matchType, clauses.type);
}


abstract production matchExpr
top::Expr ::= e::Expr clauses::SimpleMatching
{
  top.pp = "match " ++ e.pp ++ " with " ++ clauses.pp;

  restricted e.knownTypes = top.knownTypes;
  restricted clauses.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;
  restricted clauses.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;
  implicit clauses.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit clauses.subst = e.subst_out;
  implicit top.subst_out = typeUnify(e.type, clauses.matchType, clauses.subst_out);

  implicit top.type = if typeEqual(e.type, clauses.matchType, top.subst_out)
                      then clauses.type
                      end;
}


abstract production tryExpr
top::Expr ::= e::Expr clauses::SimpleMatching
{
  top.pp = "try " ++ e.pp ++ " with " ++ clauses.pp;

  restricted e.knownTypes = top.knownTypes;
  restricted clauses.knownTypes = top.knownTypes;

  restricted e.knownConstructors = top.knownConstructors;
  restricted clauses.knownConstructors = top.knownConstructors;

  implicit e.gamma = top.gamma;
  implicit clauses.gamma = top.gamma;

  implicit e.subst = top.subst;
  implicit clauses.subst = e.subst_out;
  implicit top.subst_out = typeUnify(clauses.matchType, exceptionType(),
                           typeUnify(e.type, clauses.type, clauses.subst_out));

  implicit top.type = if typeEqual(clauses.matchType, exceptionType(), top.subst_out) &&
                         typeEqual(e.type, clauses.type, top.subst_out)
                      then e.type
                      end;
}


implicit synthesized attribute matchType::Maybe<Type>;

nonterminal SimpleMatching with
   pp, knownConstructors, gamma, subst, subst_out, type, matchType, knownTypes;

abstract production simpleMatchAdd
top::SimpleMatching ::= p::Pattern e::Expr rest::SimpleMatching
{
  top.pp = p.pp ++ " -> " ++ e.pp ++ " | " ++ rest.pp;

  restricted p.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit e.gamma = p.gamma_out ++ top.gamma;
  implicit rest.gamma = top.gamma;

  implicit p.subst = top.subst;
  implicit e.subst = p.subst_out;
  implicit rest.subst = e.subst_out;
  implicit top.subst_out = typeUnify(p.type, rest.matchType,
                           typeUnify(e.type, rest.type, rest.subst_out));

  implicit top.type = if typeEqual(e.type, rest.type, top.subst_out)
                      then e.type
                      end;

  implicit top.matchType = if typeEqual(p.type, rest.matchType, top.subst_out)
                           then p.type
                           end;
}


abstract production simpleMatchEnd
top::SimpleMatching ::=
{
  top.pp = "";

  implicit top.subst_out = top.subst;

  implicit top.type = freshType();

  implicit top.matchType = freshType();
}


abstract production funExpr
top::Expr ::= clauses::MultipleMatching
{
  top.pp = "fun " ++ clauses.pp;

  restricted clauses.knownTypes = top.knownTypes;

  restricted clauses.knownConstructors = top.knownConstructors;

  implicit clauses.gamma = top.gamma;

  implicit clauses.subst = top.subst;
  implicit top.subst_out = clauses.subst_out;

  implicit top.type = buildArrowType(clauses.ptyList, clauses.type);
}


implicit synthesized attribute ptyList::Maybe<[Type]>;

nonterminal PatternList with
   pp, knownConstructors, gamma_out, ptyList, subst, subst_out, knownTypes;

abstract production patternListAdd
top::PatternList ::= p::Pattern rest::PatternList
{
  top.pp = p.pp ++ " " ++ rest.pp;

  restricted p.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted p.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit top.gamma_out = rest.gamma_out ++ p.gamma_out;

  implicit p.subst = top.subst;
  implicit rest.subst = p.subst_out;
  implicit top.subst_out = rest.subst_out;

  implicit top.ptyList = if namesDisjoint(rest.gamma_out, p.gamma_out)
                         then p.type::rest.ptyList
                         end;
}


abstract production patternListEnd
top::PatternList ::=
{
  top.pp = "";

  implicit top.gamma_out = [];

  implicit top.subst_out = top.subst;

  implicit top.ptyList = [];
}


nonterminal MultipleMatching with
   pp, knownConstructors, ptyList, type, subst, subst_out, gamma, knownTypes;

abstract production multMatchAdd
top::MultipleMatching ::= pl::PatternList e::Expr rest::MultipleMatching
{
  top.pp = pl.pp ++ " -> " ++ e.pp ++ " | " ++ rest.pp;

  restricted pl.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;
  restricted rest.knownTypes = top.knownTypes;

  restricted pl.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;
  restricted rest.knownConstructors = top.knownConstructors;

  implicit e.gamma = pl.gamma_out ++ top.gamma;
  implicit rest.gamma = top.gamma;

  implicit pl.subst = top.subst;
  implicit e.subst = pl.subst_out;
  implicit rest.subst = e.subst_out;
  implicit top.subst_out = typeListUnify(pl.ptyList, rest.ptyList,
                           typeUnify(e.type, rest.type, rest.subst_out));

  implicit top.type = if typeEqual(e.type, rest.type, top.subst_out)
                      then e.type
                      end;

  implicit top.ptyList = if typeEqual_TypeList(pl.ptyList, rest.ptyList, top.subst_out)
                         then pl.ptyList
                         end;
}

abstract production multMatchEnd
top::MultipleMatching ::= pl::PatternList e::Expr
{
  top.pp = pl.pp ++ " -> " ++ e.pp;

  restricted pl.knownTypes = top.knownTypes;
  restricted e.knownTypes = top.knownTypes;

  restricted pl.knownConstructors = top.knownConstructors;
  restricted e.knownConstructors = top.knownConstructors;

  implicit e.gamma = pl.gamma_out ++ top.gamma;

  implicit pl.subst = top.subst;
  implicit e.subst = pl.subst_out;
  implicit top.subst_out = e.subst_out;

  implicit top.type = e.type;

  implicit top.ptyList = pl.ptyList;
}

