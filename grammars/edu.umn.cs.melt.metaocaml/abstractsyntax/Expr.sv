grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

imports core:monad;
imports silver:langutil;
imports silver:langutil:pp;

synthesized attribute freeVars::[String];

nonterminal Expr with location, valueEnv, pp, freeVars, value;

abstract production varExpr
top::Expr ::= id::String
{
  top.pp = text(id);
  top.freeVars = [id];
  top.value = right(lookupBy(stringEq, id, top.valueEnv).fromJust);
}

abstract production intExpr
top::Expr ::= i::Integer
{
  top.pp = text(toString(i));
  top.freeVars = [];
  top.value = right(intValue(i));
}

abstract production letExpr
top::Expr ::= id::String t::Expr body::Expr
{
  top.pp = pp"(let ${text(id)} = ${t.pp} in ${body.pp})";
  top.freeVars = unionBy(stringEq, t.freeVars, removeBy(stringEq, id, body.freeVars));
  top.value = do (bindEither, returnEither) { t.value; body.value; };
  
  body.valueEnv = pair(id, t.value.fromRight) :: top.valueEnv;
}

abstract production letRecExpr
top::Expr ::= id::String t::Expr body::Expr
{
  top.pp = pp"(let rec ${text(id)} = ${t.pp} in ${body.pp})";
  top.freeVars = removeBy(stringEq, id, unionBy(stringEq, t.freeVars, body.freeVars));
  top.value = do (bindEither, returnEither) { t.value; body.value; };
  
  t.valueEnv = pair(id, t.value.fromRight) :: top.valueEnv;
  body.valueEnv = t.valueEnv;
}

abstract production lambdaExpr
top::Expr ::= id::String body::Expr
{
  local unfolded::Pair<[String] Expr> = unfoldLambdaVars(top);
  top.pp = pp"(fun ${ppImplode(space(), map(text, unfolded.fst))} -> ${unfolded.snd.pp})";
  top.freeVars = removeBy(stringEq, id, body.freeVars);
  top.value = right(closureValue(id, body, top.valueEnv));
}

abstract production appExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val of
      | closureValue(id, body, env) ->
        decorate body with {valueEnv = pair(id, e2Val) :: env;}.value
      | _ -> error("expected a closure value")
      end;
    };
}

abstract production ifExpr
top::Expr ::= e1::Expr e2::Expr e3::Expr
{
  top.pp = pp"(if ${e1.pp} then ${e2.pp} else ${e3.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, unionBy(stringEq, e2.freeVars, e3.freeVars));
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      case e1Val of
      | boolValue(b) -> if b then e2.value else e3.value
      | _ -> error("expected a bool value")
      end;
    };
}

abstract production mulExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} * ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(intValue(a * b))
      | _, _ -> error("expected an int value")
      end;
    };
}

abstract production divExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} / ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | _, intValue(0) -> left("Division by 0 at " ++ top.location.unparse)
      | intValue(a), intValue(b) -> right(intValue(a / b)) -- TODO: Silver bug, this should be lazy?
      | _, _ -> error("expected an int value")
      end;
    };
}

abstract production addExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} + ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(intValue(a + b))
      | _, _ -> error("expected an int value")
      end;
    };
}

abstract production subExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} - ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(intValue(a - b))
      | _, _ -> error("expected an int value")
      end;
    };
}

abstract production eqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} = ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(boolValue(a == b))
      | boolValue(a), boolValue(b) -> right(boolValue(a == b))
      | _, _ -> error("invalid values")
      end;
    };
}

abstract production neqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} <> ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(boolValue(a != b))
      | boolValue(a), boolValue(b) -> right(boolValue(a != b))
      | _, _ -> error("invalid values")
      end;
    };
}

abstract production gtExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} > ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(boolValue(a > b))
      | _, _ -> error("invalid values")
      end;
    };
}

abstract production gteExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} >= ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(boolValue(a >= b))
      | _, _ -> error("invalid values")
      end;
    };
}

abstract production ltExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} < ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(boolValue(a < b))
      | _, _ -> error("invalid values")
      end;
    };
}

abstract production lteExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} <= ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(boolValue(a <= b))
      | _, _ -> error("invalid values")
      end;
    };
}

abstract production andExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} && ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | boolValue(a), boolValue(b) -> right(boolValue(a && b))
      | _, _ -> error("expected a bool value")
      end;
    };
}

abstract production orExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} || ${e2.pp})";
  top.freeVars = unionBy(stringEq, e1.freeVars, e2.freeVars);
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | boolValue(a), boolValue(b) -> right(boolValue(a || b))
      | _, _ -> error("expected a bool value")
      end;
    };
}

function unfoldLambdaVars
Pair<[String] Expr> ::= t::Expr
{
  return
    case t of
    | lambdaExpr(n, body) ->
      let rest::Pair<[String] Expr> = unfoldLambdaVars(body)
      in pair(n :: rest.fst, rest.snd)
      end
    | _ -> pair([], t)
    end;
}
