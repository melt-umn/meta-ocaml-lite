grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;
imports silver:reflect;

autocopy attribute inQuote::Boolean;
synthesized attribute freeVars::[String];

nonterminal Expr with location, inQuote, env, valueEnv, pp, freeVars, errors, subsIn, subsOut, subsFinal, type, value<Value>;

abstract production varExpr
top::Expr ::= id::String
{
  top.pp = text(id);
  top.freeVars = [id];
  
  top.subsOut = top.subsIn;
  
  local lookupRes::Maybe<EnvItem> = lookup(id, top.env);
  top.errors :=
    case lookupRes of
    | just(i) ->
      if !top.inQuote && i.defInQuote
      then [err(top.location, s"Variable ${id} was defined in a quoted code region and cannot be used directly within an escape")]
      else []
    | nothing() -> [err(top.location, s"Variable ${id} is not defined")]
    end;
  top.type =
    case lookupRes of
    | just(i) -> i.type
    | nothing() -> freshType()
    end;
  
  top.value =
    case lookup(id, top.valueEnv) of
    | just(v) -> right(v)
    | nothing() -> error(s"Lookup of ${id} failed")
    end;
}

abstract production intExpr
top::Expr ::= i::Integer
{
  top.pp = text(toString(i));
  top.freeVars = [];
  top.errors := [];
  top.subsOut = top.subsIn;
  top.type = intType();
  top.value = right(intValue(i));
}

abstract production letExpr
top::Expr ::= id::String t::Expr body::Expr
{
  top.pp = pp"(let ${text(id)} = ${t.pp} in ${body.pp})";
  top.freeVars = union(t.freeVars, remove(id, body.freeVars));
  top.errors := t.errors ++ body.errors;
  
  t.subsIn = top.subsIn;
  body.subsIn = t.subsOut;
  top.subsOut = body.subsOut;
  
  top.type = body.type;
  top.value = applySecond(t.value, body.value);
  
  body.env = pair(id, envItem(top.inQuote, t.type)) :: top.env;
  body.valueEnv = pair(id, t.value.fromRight) :: top.valueEnv;
}

abstract production letRecExpr
top::Expr ::= id::String t::Expr body::Expr
{
  top.pp = pp"(let rec ${text(id)} = ${t.pp} in ${body.pp})";
  top.freeVars = remove(id, union(t.freeVars, body.freeVars));
  top.errors := t.errors ++ body.errors;
  
  local tType::Type = freshType();
  local tCheck::Check = typeCheck(tType, t.type, t.location);
  tCheck.subsFinal = top.subsFinal;
  top.errors <- tCheck.errors;
  
  t.subsIn = top.subsIn;
  tCheck.subsIn = t.subsOut;
  body.subsIn = tCheck.subsOut;
  top.subsOut = body.subsOut;
  
  top.type = body.type;
  top.value = applySecond(t.value, body.value);
  
  t.env = pair(id, envItem(top.inQuote, tType)) :: top.env;
  t.valueEnv = pair(id, t.value.fromRight) :: top.valueEnv;
  body.env = t.env;
  body.valueEnv = t.valueEnv;
}

abstract production lambdaExpr
top::Expr ::= id::String body::Expr
{
  local unfolded::Pair<[String] Expr> = unfoldLambdaVars(top);
  top.pp = pp"(fun ${ppImplode(space(), map(text, unfolded.fst))} -> ${unfolded.snd.pp})";
  top.freeVars = remove(id, body.freeVars);
  top.errors := body.errors;
  
  local paramType::Type = freshType();
  body.subsIn = top.subsIn;
  top.subsOut = body.subsOut;
  top.type = functionType(applySubs(body.subsOut, paramType), body.type);
  top.value = right(closureValue(id, body, top.valueEnv));
  
  body.env = pair(id, envItem(top.inQuote, paramType)) :: top.env;
}

abstract production appExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"(${e1.pp} ${e2.pp})";
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  fCheck.subsIn = e2.subsOut;
  top.subsOut = fCheck.subsOut;
  
  top.type = freshType();
  local fCheck::Check =
    typeCheck(freshenType(applySubs(e2.subsOut, e1.type)), functionType(e2.type, top.type), e1.location);
  fCheck.subsFinal = top.subsFinal;
  top.errors <- fCheck.errors;
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, union(e2.freeVars, e3.freeVars));
  top.errors := e1.errors ++ e2.errors ++ e3.errors;
  
  local cCheck::Check = typeCheck(e1.type, boolType(), e1.location);
  cCheck.subsFinal = top.subsFinal;
  top.errors <- cCheck.errors;
  local rCheck::Check = typeCheck(e2.type, e3.type, e2.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  e3.subsIn = e2.subsOut;
  cCheck.subsIn = e3.subsOut;
  rCheck.subsIn = cCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  
  top.type = e2.type;
  
  top.value =
    do {
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
  top.errors := e.errors;
  
  e.subsIn = top.subsIn;
  top.subsOut = e.subsOut;
  top.type = codeType(e.type);
  
  local a::AST = reflect(new(e));
  a.valueEnv = top.valueEnv;
  top.freeVars = a.freeVars;
  top.value =
    do {
      aVal::AST <- a.value;
      return codeValue(aVal);
    };
  
  e.inQuote = true;
}

abstract production escapeExpr
top::Expr ::= e::Expr
{
  top.pp = pp"(.~${e.pp})";
  top.freeVars = error("undefined");
  top.errors := e.errors;
  
  local cType::Type = freshType();
  local cCheck::Check = typeCheck(e.type, codeType(cType), e.location);
  cCheck.subsFinal = top.subsFinal;
  top.errors <- cCheck.errors;
  
  e.subsIn = top.subsIn;
  cCheck.subsIn = e.subsOut;
  top.subsOut = cCheck.subsOut;
  top.type = cType;
  
  top.value = error("undefined");
  
  e.inQuote = false;
}

abstract production runExpr
top::Expr ::= e::Expr
{
  top.pp = pp"(.! ${e.pp})";
  top.freeVars = e.freeVars;
  top.errors := e.errors;
  
  local cType::Type = freshType();
  local cCheck::Check = typeCheck(e.type, codeType(cType), e.location);
  cCheck.subsFinal = top.subsFinal;
  top.errors <- cCheck.errors;
  
  e.subsIn = top.subsIn;
  cCheck.subsIn = e.subsOut;
  top.subsOut = cCheck.subsOut;
  top.type = cType;
  
  top.value =
    do {
      eVal::Value <- e.value;
      let e1::Expr =
        case eVal of
        | codeValue(a) ->
          case reify(a) of
          | left(msg) -> error(s"Reification of ${show(80, a.pp)} failed: ${msg}")
          | right(e1) -> e1
          end
        | _ -> error("expected an ast value")
        end;
      case removeAll(map(fst, top.valueEnv), e1.freeVars) of
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = intType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = intType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = intType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = intType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = intType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, intType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, intType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, boolType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, boolType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
  top.freeVars = union(e1.freeVars, e2.freeVars);
  top.errors := e1.errors ++ e2.errors;
  
  local lCheck::Check = typeCheck(e1.type, boolType(), e1.location);
  lCheck.subsFinal = top.subsFinal;
  top.errors <- lCheck.errors;
  local rCheck::Check = typeCheck(e2.type, boolType(), e1.location);
  rCheck.subsFinal = top.subsFinal;
  top.errors <- rCheck.errors;
  
  e1.subsIn = top.subsIn;
  e2.subsIn = e1.subsOut;
  lCheck.subsIn = e2.subsOut;
  rCheck.subsIn = lCheck.subsOut;
  top.subsOut = rCheck.subsOut;
  top.type = boolType();
  
  top.value =
    do {
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
