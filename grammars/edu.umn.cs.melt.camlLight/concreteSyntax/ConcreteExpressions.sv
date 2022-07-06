grammar edu:umn:cs:melt:camlLight:concreteSyntax;

imports silver:langutil;



nonterminal Expression_c with ast<Expr>;

concrete productions top::Expression_c
| 'let' id::LetBindings_c 'in' e2::Expression_c
  { top.ast = letExpr(id.ast, e2.ast); }
| 'let' 'rec' id::LetBindings_c 'in' e2::Expression_c
  { top.ast = letRecExpr(id.astrec, e2.ast); }
| 'fun' m::MultipleMatching_c
  { top.ast = funExpr(m.ast); }
| 'function' s::SimpleMatching_c
  { top.ast = functionExpr(s.ast); }
| 'match' e::Expression_c 'with' s::SimpleMatching_c
  { top.ast = matchExpr(e.ast, s.ast); }
| 'try' e::Expression_c 'with' s::SimpleMatching_c
  { top.ast = tryExpr(e.ast, s.ast); }
| e::Expression1_c
  { top.ast = e.ast; }


nonterminal Expression1_c with ast<Expr>;

concrete productions top::Expression1_c
| e1::Expression_If_c ';' e2::Expression1_c
  { top.ast = exprSeq(e1.ast, e2.ast); }
| e::Expression_If_c
  { top.ast = e.ast; }


nonterminal Expression_If_c with ast<Expr>;
nonterminal Expression_IfOpen_c with ast<Expr>;
nonterminal Expression_IfClosed_c with ast<Expr>;

concrete productions top::Expression_If_c
| e::Expression_IfOpen_c
  { top.ast = e.ast; }
| e::Expression_IfClosed_c
  { top.ast = e.ast; }

concrete productions top::Expression_IfOpen_c
| 'if' c::Expression_c 'then' th::Expression_If_c
  { top.ast = ifthen(c.ast, th.ast); }
| 'if' c::Expression_c 'then' th::Expression_IfClosed_c 'else' el::Expression_IfOpen_c
  { top.ast = ifthenelse(c.ast, th.ast, el.ast); }

concrete productions top::Expression_IfClosed_c
| 'if' c::Expression_c 'then' th::Expression_IfClosed_c 'else' el::Expression_IfClosed_c
  { top.ast = ifthenelse(c.ast, th.ast, el.ast); }
| e::Expression2_c
  { top.ast = e.ast; }


nonterminal Expression2_c with ast<Expr>;

concrete productions top::Expression2_c
| e1::Expression3_c ':=' e2::Expression3_c
  { top.ast = refAssign(e1.ast, e2.ast); }
| e::Expression3_c
  { top.ast = e.ast; }


synthesized attribute ast_tc::TupleContents;

nonterminal Expression3_c with ast<Expr>, ast_tc;

concrete productions top::Expression3_c
| e1::Expr_c ',' e2::Expression3_c
  { top.ast = tuple(top.ast_tc);
    top.ast_tc = tupleContentsAdd(e1.ast, e2.ast_tc); }
| e::Expr_c
  { top.ast = e.ast;
    top.ast_tc = tupleContentsAdd(e.ast, tupleContentsEnd()); }



nonterminal Expr_c with ast<Expr>;

concrete productions top::Expr_c
| e1::Expr_c '=' e2::Expr_c
  { top.ast = eqExpr(e1.ast, e2.ast); }
| e1::Expr_c '<>' e2::Expr_c
  { top.ast = neqExpr(e1.ast, e2.ast); }
| e1::Expr_c '>' e2::Expr_c
  { top.ast = greaterExpr(e1.ast, e2.ast); }
| e1::Expr_c '>.' e2::Expr_c
  { top.ast = greaterFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c '>=' e2::Expr_c
  { top.ast = greaterEqExpr(e1.ast, e2.ast); }
| e1::Expr_c '>=.' e2::Expr_c
  { top.ast = greaterEqFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c '<' e2::Expr_c
  { top.ast = lessExpr(e1.ast, e2.ast); }
| e1::Expr_c '<.' e2::Expr_c
  { top.ast = lessFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c '<=' e2::Expr_c
  { top.ast = lessEqExpr(e1.ast, e2.ast); }
| e1::Expr_c '<=.' e2::Expr_c
  { top.ast = lessEqFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c '==' e2::Expr_c
  { top.ast = physicalEqExpr(e1.ast, e2.ast); }
| e1::Expr_c '!=' e2::Expr_c
  { top.ast = physicalNeqExpr(e1.ast, e2.ast); }
| e1::Expr_c '&' e2::Expr_c
  { top.ast = andExpr(e1.ast, e2.ast); }
| e1::Expr_c 'or' e2::Expr_c
  { top.ast = orExpr(e1.ast, e2.ast); }
| e1::Expr_c '@' e2::Expr_c
  { top.ast = listConcatenationExpr(e1.ast, e2.ast); }
| e1::Expr_c '^' e2::Expr_c
  { top.ast = stringConcatenationExpr(e1.ast, e2.ast); }
| 'not' e::Expr_c
  { top.ast = notExpr(e.ast); }
| e1::Expr_c '::' e2::Expr_c
  { top.ast = consExpr(e1.ast, e2.ast); }
| e1::Expr_c '+' e2::Expr_c
  { top.ast = plusExpr(e1.ast, e2.ast); }
| e1::Expr_c '+.' e2::Expr_c
  { top.ast = plusFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c Minus_t e2::Expr_c
  { top.ast = minusExpr(e1.ast, e2.ast); }
| e1::Expr_c MinusDot_t e2::Expr_c
  { top.ast = minusFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c '*' e2::Expr_c
  { top.ast = multExpr(e1.ast, e2.ast); }
| e1::Expr_c '*.' e2::Expr_c
  { top.ast = multFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c '/' e2::Expr_c
  { top.ast = divExpr(e1.ast, e2.ast); }
| e1::Expr_c '/.' e2::Expr_c
  { top.ast = divFloatExpr(e1.ast, e2.ast); }
| e1::Expr_c 'mod' e2::Expr_c
  { top.ast = modExpr(e1.ast, e2.ast); }
| e1::Expr_c '**' e2::Expr_c
  { top.ast = expFloatExpr(e1.ast, e2.ast); }
| PrefixMinus_t e::Expr_c
  { top.ast = negExpr(e.ast); }
| PrefixMinusDot_t e::Expr_c
  { top.ast = negFloatExpr(e.ast); }
| e::Expr17_c
  { top.ast = e.ast; }


nonterminal Expr17_c with ast<Expr>;

concrete productions top::Expr17_c
| e1::Expr17_c e2::BasicExpr_c
  { top.ast = app(e1.ast, e2.ast); }
| e::BasicExpr_c
  { top.ast = e.ast; }


nonterminal BasicExpr_c with ast<Expr>;

concrete productions top::BasicExpr_c
| e::BasicExpr_c '.(' index::Expression_c ')'
  { top.ast = arrayAccessExpr(e.ast, index.ast); }
| e1::BasicExpr_c '.(' index::Expression_c ')' '<-' e2::BasicExpr_c
  { top.ast = arrayAssignExpr(e1.ast, index.ast, e2.ast); }
| '!' e::BasicExpr_c
  { top.ast = derefExpr(e.ast); }
--
| id::Identifier_t
  { top.ast = var(id.lexeme); }
| i::IntegerLiteral_t
  { top.ast = intConst(toInteger(i.lexeme)); }
| f::FloatLiteral_Exp_t
  { top.ast = floatConst(toFloat(f.lexeme)); }
| f::FloatLiteral_Dec_t
  { top.ast = floatConst(toFloat(f.lexeme)); }
| c::CharLiteral_t
  { top.ast = charConst(substring(1, length(c.lexeme) - 1, c.lexeme)); }
| s::StringLiteral_t
  { top.ast = stringConst(substring(1, length(s.lexeme) - 1, s.lexeme)); }
| '(' ')'
  { top.ast = unitExpr(); }
| '[' ']'
  { top.ast = emptyListExpr(); }
| '[' contents::ListExpressionBuilder ']'
  { top.ast = listExpr(contents.ast); }
| '[|' contents::ListExpressionBuilder '|]'
  { top.ast = arrayExpr(contents.ast); }
| '(' e::Expression_c ')'
  { top.ast = e.ast; }
| 'begin' e::Expression_c 'end'
  { top.ast = e.ast; }
| '(' e::Expression_c ':' t::TypeExpr ')'
  { top.ast = ascriptionExpr(e.ast, t.ast); }
| 'while' c::Expression_c 'do' b::Expression_c 'done'
  { top.ast = while(c.ast, b.ast); }
| 'for' i::Identifier_t '=' starte::Expression_c 'to' ende::Expression_c 'do' e::Expression_c 'done'
  { top.ast = forTo(i.lexeme, starte.ast, ende.ast, e.ast); }
| 'for' i::Identifier_t '=' starte::Expression_c 'downto' ende::Expression_c 'do' e::Expression_c 'done'
  { top.ast = forDownto(i.lexeme, starte.ast, ende.ast, e.ast); }
  



nonterminal ListExpressionBuilder with ast<SemicolonSequence>;

concrete productions top::ListExpressionBuilder
| e::Expr_c ';' rest::ListExpressionBuilder
  { top.ast = semicolonSeqAdd(e.ast, rest.ast); }
| e::Expr_c
  { top.ast = semicolonSeqAdd(e.ast, semicolonSeqEnd()); }


nonterminal PatternList_c with ast<PatternList>;

concrete productions top::PatternList_c
| p::Pattern_Sub5 rest::PatternList_c
  { top.ast = patternListAdd(p.ast, rest.ast); }
|
  { top.ast = patternListEnd(); }


nonterminal SimpleMatching_c with ast<SimpleMatching>;

concrete productions top::SimpleMatching_c
| p::Pattern_c '->' e::Expression_c '|' rest::SimpleMatching_c
  { top.ast = simpleMatchAdd(p.ast, e.ast, rest.ast); }
| p::Pattern_c '->' e::Expression_c
  { top.ast = simpleMatchAdd(p.ast, e.ast, simpleMatchEnd()); }


nonterminal MultipleMatching_c with ast<MultipleMatching>;

concrete productions top::MultipleMatching_c
| pl::PatternList_c '->' e::Expression_c '|' rest::MultipleMatching_c
  { top.ast = multMatchAdd(pl.ast, e.ast, rest.ast); }
| pl::PatternList_c '->' e::Expression_c
  { top.ast = multMatchEnd(pl.ast, e.ast); }


synthesized attribute astrec::RecBindings;

nonterminal LetBindings_c with ast<Bindings>, astrec;

concrete productions top::LetBindings_c
| p::Pattern_c '=' e::Expression_c 'and' rest::LetBindings_c
  { top.ast = bindingsAdd(p.ast, e.ast, rest.ast);
    top.astrec = recBindingsAdd(p.ast, e.ast, rest.astrec); }
| p::Pattern_c '=' e::Expression_c
  { top.ast = bindingsAdd(p.ast, e.ast, bindingsEnd());
    top.astrec = recBindingsAdd(p.ast, e.ast, recBindingsEnd()); }

