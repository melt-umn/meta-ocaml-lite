grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

inherited attribute valueEnv::[(String, Value)];
synthesized attribute value<a>::Either<Message a>;

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
top::Value ::= id::String body::Expr env::[(String, Value)]
{
  top.pp = pp"<fun>";
}

abstract production codeValue
top::Value ::= a::AST
{
  local e::Expr = reify(^a).fromRight;
  top.pp = pp".<${e.pp}>.";
}

attribute freeVars occurs on AST, ASTs, NamedAST, NamedASTs;

attribute valueEnv occurs on AST, ASTs, NamedAST, NamedASTs;
attribute value<AST> occurs on AST;

propagate valueEnv on AST, ASTs, NamedAST, NamedASTs;
propagate freeVars on AST, ASTs, NamedAST, NamedASTs excluding nonterminalAST;

aspect default production
top::AST ::=
{
  top.value = right(^top);
}

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  local isEscape::Boolean =
    prodName == "edu:umn:cs:melt:metaocaml:abstractsyntax:escapeExpr";
  local escape::Expr =
    case children of
    | consAST(a, nilAST()) -> reify(^a).fromRight
    | _ -> error("Invalid AST for escapeExpr")
    end;
  escape.valueEnv = top.valueEnv;
  
  top.freeVars :=
    if isEscape
    then escape.freeVars
    else union(children.freeVars, annotations.freeVars);
  top.value =
    if isEscape
    then
      do {
        escapeVal::Value <- escape.value;
        return
          case escapeVal of
          | codeValue(a) -> ^a
          | _ -> error("expected an ast value")
          end;
      }
    else
      do {
        childrenValue::ASTs <- children.value;
        annotationValue::NamedASTs <- annotations.value;
        return nonterminalAST(prodName, childrenValue, annotationValue);
      };
}

aspect production listAST
top::AST ::= vals::ASTs
{
  top.value =
    do {
      valsValue::ASTs <- vals.value;
      return listAST(valsValue);
    };
}

attribute value<ASTs> occurs on ASTs;

aspect production consAST
top::ASTs ::= h::AST t::ASTs
{
  top.value =
    do {
      hValue::AST <- h.value;
      tValue::ASTs <- t.value;
      return consAST(hValue, tValue);
    };
}

aspect production nilAST
top::ASTs ::=
{
  top.value = right(nilAST());
}

attribute value<NamedASTs> occurs on NamedASTs;

aspect production consNamedAST
top::NamedASTs ::= h::NamedAST t::NamedASTs
{
  top.value =
    do {
      hValue::NamedAST <- h.value;
      tValue::NamedASTs <- t.value;
      return consNamedAST(hValue, tValue);
    };
}

aspect production nilNamedAST
top::NamedASTs ::=
{
  top.value = right(nilNamedAST());
}

attribute value<NamedAST> occurs on NamedAST;

aspect production namedAST
top::NamedAST ::= n::String v::AST
{
  top.value =
    do {
      vValue::AST <- v.value;
      return namedAST(n, vValue);
    };
}

