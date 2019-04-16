grammar edu:umn:cs:melt:metaocaml:concretesyntax;

imports silver:langutil;
imports edu:umn:cs:melt:metaocaml:abstractsyntax;

ignore terminal WhiteSpace_t /[\n\r\t\ ]+/;
ignore terminal Comment_t /\(\*([^\*]*|\*[^\)])*\*\)/;

lexer class Keyword;
terminal Fun_t  'fun'  lexer classes {Keyword}, precedence = 0;
terminal Let_t  'let'  lexer classes {Keyword}, precedence = 0;
terminal Rec_t  'rec'  lexer classes {Keyword};
terminal In_t   'in'   lexer classes {Keyword}, precedence = 0;
terminal If_t   'if'   lexer classes {Keyword};
terminal Then_t 'then' lexer classes {Keyword};
terminal Else_t 'else' lexer classes {Keyword}, precedence = 0;

terminal Identifier_t /[A-Za-z_\$][A-Za-z_0-9\$]*/ submits to {Keyword};
terminal IntConst_t /[0-9]+/;

terminal Dot_t '.';
terminal LParen_t '(';
terminal RParen_t ')';

terminal App_t '' association = left, precedence = 14;
terminal Times_t '*' association = left, precedence = 11;
terminal Divide_t '/' association = left, precedence = 11;
terminal Plus_t '+' association = left, precedence = 10;
terminal Minus_t '-' association = left, precedence = 10;
terminal Eq_t '=' association = left, precedence = 7;
terminal Neq_t '<>' association = left, precedence = 7;
terminal Gt_t '>' association = left, precedence = 7;
terminal Gte_t '>=' association = left, precedence = 7;
terminal Lt_t '<' association = left, precedence = 7;
terminal Lte_t '<=' association = left, precedence = 7;
terminal And_t '&&' association = left, precedence = 6;
terminal Or_t '||' association = left, precedence = 5;
terminal Arrow_t '->' precedence = 0;

nonterminal Expr_c with ast<Expr>, location;

concrete productions top::Expr_c
| id::Identifier_t
  { top.ast = varExpr(id.lexeme, location=top.location); }
| i::IntConst_t
  { top.ast = intExpr(toInteger(i.lexeme), location=top.location); }
| 'let' id::Identifier_t '=' e1::Expr_c 'in' e2::Expr_c
  { top.ast = letExpr(id.lexeme, e1.ast, e2.ast, location=top.location); }
| 'let' 'rec' id::Identifier_t '=' e1::Expr_c 'in' e2::Expr_c
  { top.ast = letRecExpr(id.lexeme, e1.ast, e2.ast, location=top.location); }
| 'fun' ids::Identifiers_c '->' t::Expr_c
  { top.ast = ids.ast(t.ast); }
| e1::Expr_c App_t e2::Expr_c
  { top.ast = appExpr(e1.ast, e2.ast, location=top.location); }
| 'if' e1::Expr_c 'then' e2::Expr_c 'else' e3::Expr_c
  { top.ast = ifExpr(e1.ast, e2.ast, e3.ast, location=top.location); }
| e1::Expr_c '*' e2::Expr_c
  { top.ast = mulExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '/' e2::Expr_c
  { top.ast = divExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '+' e2::Expr_c
  { top.ast = addExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '-' e2::Expr_c
  { top.ast = subExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '=' e2::Expr_c
  { top.ast = eqExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '<>' e2::Expr_c
  { top.ast = neqExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '>' e2::Expr_c
  { top.ast = gtExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '>=' e2::Expr_c
  { top.ast = gteExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '<' e2::Expr_c
  { top.ast = ltExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '<=' e2::Expr_c
  { top.ast = lteExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '&&' e2::Expr_c
  { top.ast = andExpr(e1.ast, e2.ast, location=top.location); }
| e1::Expr_c '||' e2::Expr_c
  { top.ast = orExpr(e1.ast, e2.ast, location=top.location); }
| '(' t::Expr_c ')'
  { top.ast = t.ast; }

nonterminal Identifiers_c with ast<(Expr ::= Expr)>, location;

concrete productions top::Identifiers_c
| h::Identifier_t t::Identifiers_c
  { top.ast = \ b::Expr -> lambdaExpr(h.lexeme, t.ast(b), location=h.location); }
| h::Identifier_t
  { top.ast = lambdaExpr(h.lexeme, _, location=h.location); }
