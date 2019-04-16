grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

autocopy attribute valueEnv::[Pair<String Value>];
synthesized attribute value<a>::Either<String a>;

nonterminal Value with pp;

abstract production intValue
top::Value ::= i::Integer
{
  top.pp = text(toString(i));
}

abstract production boolValue
top::Value ::= b::Boolean
{
  top.pp = text(toString(b));
}

abstract production closureValue
top::Value ::= id::String body::Expr env::[Pair<String Value>]
{
  top.pp = pp"<fun>";
}

abstract production astValue
top::Value ::= a::AST
{
  local e::Expr = reify(a).fromRight;
  top.pp = pp".<${e.pp}>.";
}

attribute freeVars occurs on AST, ASTs, NamedAST, NamedASTs;

attribute valueEnv occurs on AST, ASTs, NamedAST, NamedASTs;
attribute value<AST> occurs on AST;

aspect default production
top::AST ::=
{
  top.freeVars = [];
  top.value = right(top);
}

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  local isEscape::Boolean = prodName == "edu:umn:cs:melt:metaocaml:abstractsyntax:escapeExpr";
  local escape::Expr =
    case children of
    | consAST(a, nilAST()) -> reify(a).fromRight
    end;
  escape.valueEnv = top.valueEnv;
  
  top.freeVars =
    if isEscape
    then escape.freeVars
    else unionBy(stringEq, children.freeVars, annotations.freeVars);
  top.value =
    if isEscape
    then
      do (bindEither, returnEither) {
        escapeVal::Value <- escape.value;
        return
          case escapeVal of
          | astValue(a) -> a
          | _ -> error("expected an ast value")
          end;
      }
    else
      do (bindEither, returnEither) {
        childrenValue::ASTs <- children.value;
        annotationValue::NamedASTs <- annotations.value;
        return nonterminalAST(prodName, childrenValue, annotationValue);
      };
}

aspect production listAST
top::AST ::= vals::ASTs
{
  top.freeVars = vals.freeVars;
  top.value =
    do (bindEither, returnEither) {
      valsValue::ASTs <- vals.value;
      return listAST(valsValue);
    };
}

attribute value<ASTs> occurs on ASTs;

aspect production consAST
top::ASTs ::= h::AST t::ASTs
{
  top.freeVars = unionBy(stringEq, h.freeVars, t.freeVars);
  top.value =
    do (bindEither, returnEither) {
      hValue::AST <- h.value;
      tValue::ASTs <- t.value;
      return consAST(hValue, tValue);
    };
}

aspect production nilAST
top::ASTs ::=
{
  top.freeVars = [];
  top.value = right(nilAST());
}

attribute value<NamedASTs> occurs on NamedASTs;

aspect production consNamedAST
top::NamedASTs ::= h::NamedAST t::NamedASTs
{
  top.freeVars = unionBy(stringEq, h.freeVars, t.freeVars);
  top.value =
    do (bindEither, returnEither) {
      hValue::NamedAST <- h.value;
      tValue::NamedASTs <- t.value;
      return consNamedAST(hValue, tValue);
    };
}

aspect production nilNamedAST
top::NamedASTs ::=
{
  top.freeVars = [];
  top.value = right(nilNamedAST());
}

attribute value<NamedAST> occurs on NamedAST;

aspect production namedAST
top::NamedAST ::= n::String v::AST
{
  top.freeVars = v.freeVars;
  top.value =
    do (bindEither, returnEither) {
      vValue::AST <- v.value;
      return namedAST(n, vValue);
    };
}

