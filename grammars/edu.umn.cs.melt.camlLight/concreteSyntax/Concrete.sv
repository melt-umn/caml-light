grammar edu:umn:cs:melt:camlLight:concreteSyntax;


imports edu:umn:cs:melt:camlLight:abstractSyntax;


ignore terminal Blank_t /[\t\r\n\ ]+/;

ignore terminal Comment_t /\(\*([^\*]*|\*[^\)])*\*\)/;

--need to ignore nested comments delimited by (* and *)

terminal Identifier_t /[A-Za-z][A-Za-z0-9_]*/ submits to {KEYWORD};

terminal IntegerLiteral_t /-?(([0-9]+)|((0x|0X)[0-9A-Fa-f]+)|((0o|0O)[0-7]+)|((0b|0B)[01]+))/;

--Since floats can omit either the decimal or the exponent but not both, we need two regexes
terminal FloatLiteral_Dec_t /-?[0-9]+\.[0-9]+([eE](+-)?[0-9]+)?/;
terminal FloatLiteral_Exp_t /-?[0-9]+[eE](+-)?[0-9]+/;

terminal CharLiteral_t /'([^'\\])|(\\[\\'ntbr])|(\\[0-9][0-9][0-9])'/;

terminal StringLiteral_t /"([^\\"]|(\\[\\"ntbr])|(\\[0-9][0-9][0-9]))*"/;


lexer class KEYWORD;

terminal And_t        'and'         lexer classes {KEYWORD};
terminal As_t         'as'          lexer classes {KEYWORD};
terminal Begin_t      'begin'       lexer classes {KEYWORD};
terminal Do_t         'do'          lexer classes {KEYWORD};
terminal Done_t       'done'        lexer classes {KEYWORD};
terminal Downto_t     'downto'      lexer classes {KEYWORD};
terminal Else_t       'else'        lexer classes {KEYWORD}, precedence = 0;
terminal End_t        'end'         lexer classes {KEYWORD};
terminal Exception_t  'exception'   lexer classes {KEYWORD};
terminal For_t        'for'         lexer classes {KEYWORD};
terminal Fun_t        'fun'         lexer classes {KEYWORD}, precedence = 0;
terminal Function_t   'function'    lexer classes {KEYWORD}, precedence = 0;
terminal If_t         'if'          lexer classes {KEYWORD}, precedence = 2;
terminal In_t         'in'          lexer classes {KEYWORD}, precedence = 0;
terminal Let_t        'let'         lexer classes {KEYWORD}, precedence = 0;
terminal Match_t      'match'       lexer classes {KEYWORD}, precedence = 0;
terminal Mutable_t    'mutable'     lexer classes {KEYWORD};
terminal Not_t        'not'         lexer classes {KEYWORD}, precedence = 7;
terminal Of_t         'of'          lexer classes {KEYWORD};
terminal Or_t         'or'          lexer classes {KEYWORD}, precedence = 5, association=left;
terminal Prefix_t     'prefix'      lexer classes {KEYWORD};
terminal Rec_t        'rec'         lexer classes {KEYWORD};
terminal Then_t       'then'        lexer classes {KEYWORD};
terminal To_t         'to'          lexer classes {KEYWORD};
terminal Try_t        'try'         lexer classes {KEYWORD}, precedence = 0;
terminal Type_t       'type'        lexer classes {KEYWORD};
terminal Value_t      'value'       lexer classes {KEYWORD};
terminal Where_t      'where'       lexer classes {KEYWORD};
terminal While_t      'while'       lexer classes {KEYWORD};
terminal With_t       'with'        lexer classes {KEYWORD};

terminal Octothorpe_t             '#'    lexer classes {KEYWORD};
terminal Bang_t                   '!'    lexer classes {KEYWORD},                    precedence = 19;
terminal BangEq_t                 '!='   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal Ampersand_t              '&'    lexer classes {KEYWORD}, association=left,  precedence = 6;
terminal LeftParen_t              '('    lexer classes {KEYWORD};
terminal RightParen_t             ')'    lexer classes {KEYWORD};
terminal Asterisk_t               '*'    lexer classes {KEYWORD}, association=left,  precedence = 12;
terminal AsteriskDot_t            '*.'   lexer classes {KEYWORD}, association=left,  precedence = 12;
terminal Plus_t                   '+'    lexer classes {KEYWORD}, association=left,  precedence = 11;
terminal PlusDot_t                '+.'   lexer classes {KEYWORD}, association=left,  precedence = 11;
terminal Comma_t                  ','    lexer classes {KEYWORD}, association=right, precedence = 4;
terminal Minus_t                  '-'    lexer classes {KEYWORD}, association=left,  precedence = 11;
terminal MinusDot_t               '-.'   lexer classes {KEYWORD}, association=left,  precedence = 11;
terminal ForwardArrow_t           '->'   lexer classes {KEYWORD}, association=right, precedence = 0;
terminal Dot_t                    '.'    lexer classes {KEYWORD},                    precedence = 18;
terminal DotLeftParent_t          '.('   lexer classes {KEYWORD},                    precedence = 18;
terminal Slash_t                  '/'    lexer classes {KEYWORD}, association=left,  precedence = 12;
terminal SlashDot_t               '/.'   lexer classes {KEYWORD}, association=left,  precedence = 12;
terminal Colon_t                  ':'    lexer classes {KEYWORD};
terminal ColonColon_t             '::'   lexer classes {KEYWORD}, association=right, precedence = 10;
terminal ColonEq_t                ':='   lexer classes {KEYWORD}, association=right, precedence = 3;
terminal Semicolon_t              ';'    lexer classes {KEYWORD}, association=right, precedence = 1;
terminal SemicolonSemicolon_t     ';;'   lexer classes {KEYWORD};
terminal Less_t                   '<'    lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal LessDot_t                '<.'   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal BackArrow_t              '<-'   lexer classes {KEYWORD}, association=right, precedence = 3;
terminal LessEq_t                 '<='   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal LessEqDot_t              '<=.'  lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal Neq_t                    '<>'   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal NeqDot_t                 '<>.'  lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal Eq_t                     '='    lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal EqDot_t                  '=.'   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal EqEq_t                   '=='   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal Greater_t                '>'    lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal GreaterDot_t             '>.'   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal GreaterEq_t              '>='   lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal GreaterEqDot_t           '>=.'  lexer classes {KEYWORD}, association=left,  precedence = 8;
terminal AtSign_t                 '@'    lexer classes {KEYWORD}, association=right, precedence = 9;
terminal LeftBracket_t            '['    lexer classes {KEYWORD};
terminal LeftBracketBar_t         '[|'   lexer classes {KEYWORD};
terminal RightBracket_t           ']'    lexer classes {KEYWORD};
terminal Up_t                     '^'    lexer classes {KEYWORD}, association=right, precedence = 9;
terminal Underscore_t             '_'    lexer classes {KEYWORD};
terminal UnderscoreUnderscore_t   '__'   lexer classes {KEYWORD};
terminal LeftCurly_t              '{'    lexer classes {KEYWORD};
terminal Bar_t                    '|'    lexer classes {KEYWORD}, association=left, precedence = 3;
terminal RightBracketBar_t        '|]'   lexer classes {KEYWORD};
terminal RightCurly_t             '}'    lexer classes {KEYWORD};
terminal Tick_t                   /'/    lexer classes {KEYWORD};

terminal Mod_t                    'mod'  lexer classes {KEYWORD}, association=left,  precedence = 13;
terminal AsteriskAsterisk_t       '**'   lexer classes {KEYWORD}, association=right, precedence = 14;
terminal PrefixMinus_t            '-'    lexer classes {KEYWORD},                    precedence = 15;
terminal PrefixMinusDot_t         '-.'   lexer classes {KEYWORD},                    precedence = 15;




synthesized attribute ast<a>::a;



--Type Expressions
nonterminal TypeExpr with ast<Type>;
nonterminal TypeExpr_Sub1 with ast<Type>;
nonterminal TypeExpr_Sub2 with ast<Type>;

concrete productions top::TypeExpr
| te1::TypeExpr '->' te2::TypeExpr
  { top.ast = arrowType(te1.ast, te2.ast); }
| te::TypeExpr_Sub1
  { top.ast = te.ast; }


concrete productions top::TypeExpr_Sub1
| te::TypeExpr_Sub2 rest::TupleTypeBuilder
  { top.ast = tupleType(tupleTyBuildAdd(te.ast, rest.ast)); }
| te::TypeExpr_Sub2
  { top.ast = te.ast; }


concrete productions top::TypeExpr_Sub2
| t::Tick_t name::Identifier_t
  { top.ast = tyVar(name.lexeme); }
| name::Identifier_t
  { top.ast = case name.lexeme of
              | "int" -> intType()
              | "float" -> floatType()
              | "bool" -> boolType()
              | "exception" -> exceptionType()
              | "unit" -> unitType()
              | "char" -> charType()
              | "string" -> stringType()
              | _ -> parameterizedTyConstructor([], name.lexeme)
              end; }
| te::TypeExpr_Sub2 name::Identifier_t
  { top.ast = parameterizedTyConstructor([te.ast], name.lexeme); }
| '(' te::TypeExpr rest::TypeArgsList ')' name::Identifier_t
  { top.ast = parameterizedTyConstructor([te.ast] ++ rest.ast, name.lexeme); }
| '(' te::TypeExpr ')'
  { top.ast = te.ast; }


nonterminal TupleTypeBuilder with ast<TupleTyBuild>;

concrete productions top::TupleTypeBuilder
| '*' te::TypeExpr_Sub2 rest::TupleTypeBuilder
  { top.ast = tupleTyBuildAdd(te.ast, rest.ast); }
| '*' te::TypeExpr_Sub2
  { top.ast = tupleTyBuildAdd(te.ast, tupleTyBuildEnd()); }


nonterminal TypeArgsList with ast<[Type]>;

concrete productions top::TypeArgsList
| ',' te::TypeExpr rest::TypeArgsList
  { top.ast = [te.ast] ++ rest.ast; }
| ',' te::TypeExpr
  { top.ast = [te.ast]; }



--Patterns
nonterminal Pattern_c with ast<Pattern>;
nonterminal Pattern_Sub1 with ast<Pattern>;
nonterminal Pattern_Sub2 with ast<Pattern>;
nonterminal Pattern_Sub3 with ast<Pattern>;
nonterminal Pattern_Sub4 with ast<Pattern>;
nonterminal Pattern_Sub5 with ast<Pattern>;


concrete productions top::Pattern_c
| p::Pattern_c 'as' name::Identifier_t
  { top.ast = namedPattern(p.ast, name.lexeme); }
| p::Pattern_Sub1
  { top.ast = p.ast; }


concrete productions top::Pattern_Sub1
| p1::Pattern_Sub2 '|' p2::Pattern_Sub1
  { top.ast = optionPattern(p1.ast, p2.ast); }
| p::Pattern_Sub2
  { top.ast = p.ast; }


concrete productions top::Pattern_Sub2
| p::Pattern_Sub3 tp::TuplePatternBuilder --tp starts with a comma
  { top.ast = tuplePattern(tuplePatternContentsAdd(p.ast, tp.ast)); }
| p::Pattern_Sub3
  { top.ast = p.ast; }


concrete productions top::Pattern_Sub3
| hd::Pattern_Sub4 '::' tl::Pattern_Sub3
  { top.ast = consPattern(hd.ast, tl.ast); }
| p::Pattern_Sub4
  { top.ast = p.ast; }


concrete productions top::Pattern_Sub4
| name::Identifier_t children::Pattern_Sub5
  { top.ast = constructorPattern(name.lexeme, children.ast); }
| p::Pattern_Sub5
  { top.ast = p.ast; }


concrete productions top::Pattern_Sub5
| '(' p::Pattern_c ':' te::TypeExpr ')'
  { top.ast = ascriptionPattern(p.ast, te.ast); }
| '(' p::Pattern_c ')'
  { top.ast = p.ast; }
| i::IntegerLiteral_t
  { top.ast = intPattern(toInteger(i.lexeme)); }
| f::FloatLiteral_Dec_t
  { top.ast = floatPattern(toFloat(f.lexeme)); }
| f::FloatLiteral_Exp_t
  { top.ast = floatPattern(toFloat(f.lexeme)); }
| c::CharLiteral_t
  { top.ast = charPattern(substring(1, 3, c.lexeme)); }
| s::StringLiteral_t
  { top.ast = stringPattern(substring(1, length(s.lexeme) - 1, s.lexeme)); }
| '[' ']'
  { top.ast = listPattern(listPatternContentsEnd()); }
| '(' ')'
  { top.ast = unitPattern(); }
| '_'
  { top.ast = defaultPattern(); }
| '[' p::Pattern_c rest::ListPatternBuilder ']'
  { top.ast = listPattern(listPatternContentsAdd(p.ast, rest.ast)); }
--For some reason this is giving an error
| name::Identifier_t
  { top.ast = simpleNamePattern(name.lexeme); }


nonterminal TuplePatternBuilder with ast<TuplePatternContents>;

concrete productions top::TuplePatternBuilder
| ',' p::Pattern_Sub3 rest::TuplePatternBuilder
  { top.ast = tuplePatternContentsAdd(p.ast, rest.ast); }
| ',' p::Pattern_Sub3
  { top.ast = tuplePatternContentsAdd(p.ast, tuplePatternContentsEnd()); }


nonterminal ListPatternBuilder with ast<ListPatternContents>;

concrete productions top::ListPatternBuilder
| ';' p::Pattern_c rest::ListPatternBuilder
  { top.ast = listPatternContentsAdd(p.ast, rest.ast); }
| 
  { top.ast = listPatternContentsEnd(); }



--Type Definitions
nonterminal TypeDefinition_c with ast<TypeDefinition>;

concrete productions top::TypeDefinition_c
| 'type' td::TypeDefs_c
  { top.ast = tyDefinition(td.ast); }


nonterminal TypeDefs_c with ast<TypeDefs>;

concrete productions top::TypeDefs_c
| td::TypeDef_c 'and' rest::TypeDefs_c
  { top.ast = typeDefsAdd(td.ast, rest.ast); }
| td::TypeDef_c
  { top.ast = typeDefsAdd(td.ast, typeDefsEnd()); }


nonterminal TypeDef_c with ast<TypeDef>;

concrete productions top::TypeDef_c
| tp::TypeParams_c name::Identifier_t '=' cd::ConstructorDecls
  { top.ast = inductiveTypeDef(tp.ast, name.lexeme, cd.ast); }
| tp::TypeParams_c name::Identifier_t '==' ty::TypeExpr
  { top.ast = aliasTypeDef(tp.ast, name.lexeme, ty.ast); }
| tp::TypeParams_c name::Identifier_t
  { top.ast = undefinedTypeDef(tp.ast, name.lexeme); }


nonterminal ConstructorDecls with ast<Constructors>;

concrete productions top::ConstructorDecls
| cd::ConstructorDecl '|' rest::ConstructorDecls
  { top.ast = constructorsAdd(cd.ast, rest.ast); }
| cd::ConstructorDecl
  { top.ast = constructorsAdd(cd.ast, constructorsEnd()); }


nonterminal LabelDecls with ast<Labels>;

concrete productions top::LabelDecls
| ld::LabelDecl ';' rest::LabelDecls
  { top.ast = labelsAdd(ld.ast, rest.ast); }
| ld::LabelDecl
  { top.ast = labelsAdd(ld.ast, labelsEnd()); }


nonterminal ConstructorDecl with ast<Constructor>;

concrete productions top::ConstructorDecl
| name::Identifier_t
  { top.ast = constructorNoParams(name.lexeme); }
| name::Identifier_t 'of' ty::TypeExpr
  { top.ast = constructorParams(name.lexeme, ty.ast); }


nonterminal LabelDecl with ast<Label>;

concrete productions top::LabelDecl
| name::Identifier_t ':' ty::TypeExpr
  { top.ast = labelImmutable(name.lexeme, ty.ast); }
| 'mutable' name::Identifier_t ':' ty::TypeExpr
  { top.ast = labelMutable(name.lexeme, ty.ast); }


nonterminal TypeParams_c with ast<TypeParams>;

concrete productions top::TypeParams_c
|
  { top.ast = typeParamsEnd(); }
| Tick_t name::Identifier_t
  { top.ast = typeParamsAdd(name.lexeme, typeParamsEnd()); }
| '(' tl::TickTyList ')'
  { top.ast = tl.ast; }


nonterminal TickTyList with ast<TypeParams>;

concrete productions top::TickTyList
| Tick_t name::Identifier_t ',' rest::TickTyList
  { top.ast = typeParamsAdd(name.lexeme, rest.ast); }
| Tick_t name::Identifier_t
  { top.ast = typeParamsAdd(name.lexeme, typeParamsEnd()); }


nonterminal ExceptionDecl with ast<ExceptionDef>;

concrete productions top::ExceptionDecl
| 'exception' cd::ConstructorDecls
  { top.ast = excDef(cd.ast); }




nonterminal TopLevel_c with ast<TopLevel>;

concrete productions top::TopLevel_c
| ed::ExceptionDecl ';;' rest::TopLevel_c
  { top.ast = excDefTopLevel(ed.ast, rest.ast); }
| td::TypeDefinition_c ';;' rest::TopLevel_c
  { top.ast = tyDefTopLevel(td.ast, rest.ast); }
| e::Expression_c ';;' rest::TopLevel_c
  { top.ast = exprTopLevel(e.ast, rest.ast); }
|
  { top.ast = topLevelEnd(); }


nonterminal Root_c with ast<Root>;

concrete productions top::Root_c
| t::TopLevel_c
  { top.ast = root(t.ast); }





