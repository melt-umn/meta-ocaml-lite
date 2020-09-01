grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

imports core:monad;
imports silver:langutil;
imports silver:langutil:pp;
imports silver:reflect;

-- TODO: fix collection attributes to not need this
function unionByStringEq
[String] ::= a::[String] b::[String]
{
  return unionBy(stringEq, a, b);
}

inherited attribute inQuote::Boolean;
monoid attribute freeVars::[String] with [], unionByStringEq;

nonterminal Expr with location, inQuote, env, valueEnv, pp, freeVars, errors, subsIn, subsOut, subsFinal, type, value<Value>;

propagate errors, subsFinal on Expr;
propagate inQuote on Expr excluding quoteExpr, escapeExpr;
propagate env, valueEnv, freeVars on Expr excluding letExpr, letRecExpr, lambdaExpr;

abstract production varExpr
top::Expr ::= id::String
{
  top.pp = text(id);
  top.freeVars <- [id];
  
  propagate subsIn, subsOut;
  
  local lookupRes::Maybe<EnvItem> = lookupBy(stringEq, id, top.env);
  top.errors <-
    case lookupRes of
    | just(i) ->
      if !top.inQuote && i.defInQuote
      then [err(top.location, s"Variable ${id} was defined in a quoted code region and cannot be used directly within an escape")]
      else []
    | nothing() -> [err(top.location, s"Variable ${id} is not defined")]
    end;
  top.type =
    case lookupRes of
    | just(i) -> freshenType(i.polyVars, i.type)
    | nothing() -> freshType()
    end;
  
  top.value =
    case lookupBy(stringEq, id, top.valueEnv) of
    | just(v) -> right(v)
    | nothing() -> error(s"Lookup of ${id} failed")
    end;
}

abstract production intExpr
top::Expr ::= i::Integer
{
  top.pp = text(toString(i));
  propagate subsIn, subsOut;
  top.type = intType();
  top.value = right(intValue(i));
}

abstract production letExpr
top::Expr ::= id::String t::Expr body::Expr
{
  top.pp = pp"(let ${text(id)} = ${t.pp} in ${body.pp})";
  top.freeVars := unionBy(stringEq, t.freeVars, removeBy(stringEq, id, body.freeVars));
  
  propagate subsIn, subsOut;
  
  top.type = body.type;
  top.value = do (bindEither, returnEither) { t.value; body.value; };
  
  t.env = top.env;
  t.valueEnv = top.valueEnv;
  
  local polyVars::[String] = removeAllBy(stringEq, envFreeVars(top.env), t.type.freeVars);
  body.env = pair(id, envItem(top.inQuote, polyVars, applySubs(t.subsOut, t.type))) :: top.env;
  body.valueEnv = pair(id, t.value.fromRight) :: top.valueEnv;
}

abstract production letRecExpr
top::Expr ::= id::String t::Expr body::Expr
{
  top.pp = pp"(let rec ${text(id)} = ${t.pp} in ${body.pp})";
  top.freeVars := removeBy(stringEq, id, unionBy(stringEq, t.freeVars, body.freeVars));
  
  local tType::Type = freshType();
  local tCheck::Check = typeCheck(tType, t.type, t.location);
  tCheck.subsFinal = top.subsFinal;
  top.errors <- tCheck.errors;
  
  thread subsIn, subsOut on top, t, tCheck, body, top;
  
  top.type = body.type;
  top.value = do (bindEither, returnEither) { t.value; body.value; };
  
  local polyVars::[String] = removeAllBy(stringEq, envFreeVars(top.env), t.type.freeVars);
  t.env = pair(id, envItem(top.inQuote, [], tType)) :: top.env;
  t.valueEnv = pair(id, t.value.fromRight) :: top.valueEnv;
  body.env = pair(id, envItem(top.inQuote, polyVars, applySubs(t.subsOut, tType))) :: top.env;
  body.valueEnv = t.valueEnv;
}

abstract production lambdaExpr
top::Expr ::= id::String body::Expr
{
  local unfolded::Pair<[String] Expr> = unfoldLambdaVars(top);
  top.pp = pp"(fun ${ppImplode(space(), map(text, unfolded.fst))} -> ${unfolded.snd.pp})";
  top.freeVars := removeBy(stringEq, id, body.freeVars);
  
  propagate subsIn, subsOut;
  
  local paramType::Type = freshType();
  top.type = functionType(paramType, body.type);
  top.value = right(closureValue(id, body, top.valueEnv));
  
  body.env = pair(id, envItem(top.inQuote, [], paramType)) :: top.env;
}

abstract production appExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} ${e2.pp})";
  
  top.type = freshType();
  local fCheck::Check = typeCheck(e1.type, functionType(e2.type, top.type), e1.location);
  fCheck.subsFinal = top.subsFinal;
  top.errors <- fCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, fCheck, top;
  
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
  
  local cCheck::Check = typeCheck(e1.type, boolType(), e1.location);
  cCheck.subsFinal = top.subsFinal;
  top.errors <- cCheck.errors;
  local rCheck::Check = typeCheck(e2.type, e3.type, e2.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, e3, cCheck, rCheck, top;
  
  top.type = e2.type;
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      case e1Val of
      | boolValue(b) -> if b then e2.value else e3.value
      | _ -> error("expected a bool value")
      end;
    };
}

-- Meta-constructs
abstract production quoteExpr
top::Expr ::= e::Expr
{
  top.pp = pp".<${e.pp}>.";
  
  propagate subsIn, subsOut;
  
  top.type = codeType(e.type);
  
  local a::AST = reflect(new(e));
  a.valueEnv = top.valueEnv;
  top.value =
    do (bindEither, returnEither) {
      aVal::AST <- a.value;
      return codeValue(aVal);
    };
  
  e.inQuote = true;
}

abstract production escapeExpr
top::Expr ::= e::Expr
{
  top.pp = pp"(.~${e.pp})";
  top.freeVars <- error("undefined");
  
  local cType::Type = freshType();
  local cCheck::Check = typeCheck(e.type, codeType(cType), e.location);
  cCheck.subsFinal = top.subsFinal;
  top.errors <- cCheck.errors;
  
  thread subsIn, subsOut on top, e, cCheck, top;
  
  top.type = cType;
  top.value = error("undefined");
  
  e.inQuote = false;
}

abstract production runExpr
top::Expr ::= e::Expr
{
  top.pp = pp"(.! ${e.pp})";
  
  local cType::Type = freshType();
  local cCheck::Check = typeCheck(e.type, codeType(cType), e.location);
  cCheck.subsFinal = top.subsFinal;
  top.errors <- cCheck.errors;
  
  thread subsIn, subsOut on top, e, cCheck, top;
  top.type = cType;
  
  top.value =
    do (bindEither, returnEither) {
      eVal::Value <- e.value;
      e1::Expr =
        case eVal of
        | codeValue(a) ->
          case reify(a) of
          | left(msg) -> error(s"Reification of ${show(80, a.pp)} failed: ${msg}")
          | right(e1) -> e1
          end
        | _ -> error("expected an ast value")
        end;
      case removeAllBy(stringEq, map(fst, top.valueEnv), e1.freeVars) of
      | [] -> right(unit())
      | vs -> left(err(e1.location, s"Run expression ${show(80, e1.pp)} contains variables ${implode(", ", vs)} bound in escaped code"))
      end;
      decorate e1 with {valueEnv = top.valueEnv;}.value;
    };
}

-- Misc. operators
abstract production modExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} mod ${e2.pp})";
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = intType();
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | intValue(a), intValue(b) -> right(intValue(a % b))
      | _, _ -> error("expected an int value")
      end;
    };
}

abstract production mulExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} * ${e2.pp})";
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = intType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = intType();
  top.value =
    do (bindEither, returnEither) {
      e1Val::Value <- e1.value;
      e2Val::Value <- e2.value;
      case e1Val, e2Val of
      | _, intValue(0) -> left(err(top.location, "Division by 0"))
      | intValue(a), intValue(b) -> right(intValue(a / b)) -- TODO: Silver bug, this should be lazy?
      | _, _ -> error("expected an int value")
      end;
    };
}

abstract production addExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} + ${e2.pp})";
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = intType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = intType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, boolType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, boolType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
  
  local lCheck::Check = typeCheck(e1.type, boolType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, boolType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  thread subsIn, subsOut on top, e1, e2, lCheck, rCheck, top;
  
  top.type = boolType();
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
