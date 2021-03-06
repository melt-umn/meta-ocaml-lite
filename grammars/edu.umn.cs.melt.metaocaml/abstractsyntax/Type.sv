grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

synthesized attribute type::Type;

synthesized attribute wrapPP::Boolean;

type Subs = [Pair<String Type>];
threaded attribute subsIn, subsOut :: Subs;
inherited attribute subsFinal::Subs;
unification attribute unifyWith {unifyWith, subsIn}, unifiesPartial, unifies;
synthesized attribute subsOutPartial::Subs;

functor attribute substituted;

nonterminal Type with pp, wrapPP, freeVars, unifyWith, unifiesPartial, unifies, subsIn, subsOut, subsOutPartial, subsFinal, substituted;

propagate freeVars on Type;
propagate unifyWith, unifies on Type;
propagate unifiesPartial on Type excluding errorType, varType;
propagate subsFinal, substituted on Type excluding varType;

aspect default production
top::Type ::=
{
  top.subsOut =
    if top.unifiesPartial
    then top.subsOutPartial
    else if top.unifyWith.unifiesPartial
    then top.unifyWith.subsOutPartial
    else top.subsIn;
}

abstract production errorType
top::Type ::=
{
  top.pp = pp"<err>";
  top.wrapPP = false;
  top.unifiesPartial = true;
  top.subsOutPartial = top.subsIn;
}

abstract production varType
top::Type ::= n::String
{
  top.pp = pp"'${text(n)}";
  top.wrapPP = false;
  top.freeVars <- [n];
  
  local isBound::Boolean = lookup(n, top.subsIn).isJust;
  local boundType::Type = lookup(n, top.subsIn).fromJust;
  boundType.unifyWith = otherType;
  boundType.subsIn = top.subsIn;
  local otherType::Type = new(top.unifyWith);
  otherType.unifyWith = boundType;
  otherType.subsIn = top.subsIn;
  top.unifiesPartial =
    case top.unifyWith of
    | varType(n1) when n == n1 -> true
    | _ when isBound -> boundType.unifies
    | _ -> !contains(n, top.unifyWith.freeVars) -- occurs check
    end;
  top.subsOutPartial =
    case top.unifyWith of
    | varType(n1) when n == n1 -> []
    | _ when isBound -> boundType.subsOut
    | _ -> pair(n, otherType) :: top.subsIn
    end;

  top.substituted =
    case lookup(n, top.subsFinal) of
    | just(a) -> applySubs(top.subsFinal, a)
    | nothing() -> top
    end;
}

abstract production skolemType
top::Type ::= n::String
{
  top.pp = pp"'${text(n)}";
  top.wrapPP = false;
  top.freeVars <- [n];
  top.subsOutPartial = top.subsIn;
}

abstract production intType
top::Type ::=
{
  top.pp = pp"int";
  top.wrapPP = false;
  top.subsOutPartial = top.subsIn;
}

abstract production boolType
top::Type ::=
{
  top.pp = pp"bool";
  top.wrapPP = false;
  top.subsOutPartial = top.subsIn;
}

abstract production functionType
top::Type ::= a::Type b::Type
{
  top.pp = pp"${maybeWrapTypePP(a)} -> ${b.pp}";
  top.wrapPP = true;

  thread subsIn, subsOut on top, a, b;
  top.subsOutPartial = b.subsOut;
}

abstract production codeType
top::Type ::= a::Type
{
  top.pp = pp"${maybeWrapTypePP(a)} code";
  top.wrapPP = true;

  thread subsIn, subsOut on top, a;
  top.subsOutPartial = a.subsOut;
}

nonterminal Check with subsIn, subsOut, subsFinal, errors;

propagate subsFinal on Check;

abstract production typeCheck
top::Check ::= a::Type b::Type loc::Location
{
  a.unifyWith = b;
  b.unifyWith = a;
  thread subsIn, subsOut on top, a, top;
  thread subsIn, subsOut on top, b;
  local finalA::Type = applySubs(top.subsFinal, a);
  local finalB::Type = applySubs(top.subsFinal, b);
  top.errors :=
    if a.unifies
    then []
    else [err(loc, s"Incompatible types ${show(80, finalA.pp)} and ${show(80, finalB.pp)}")];
}

-- Not used, but for reference
function unify
Maybe<Subs> ::= a::Type b::Type
{
  a.unifyWith = b;
  a.subsIn = [];
  b.unifyWith = a;
  b.subsIn = [];
  return if a.unifies then just(a.subsOut) else nothing();
}

function applySubs
Type ::= s::Subs t::Type
{
  t.subsFinal = s;
  return t.substituted;
}

function showSubs
String ::= subs::Subs
{
  return implode(", ", map(\ s::Pair<String Type> -> s"${s.fst} = ${show(80, s.snd.pp)}", subs));
}

function freshType
Type ::=
{
  return varType("a" ++ toString(genInt()));
}

function freshenType
Type ::= vars::[String] a::Type
{
  return applySubs(zipWith(pair, vars, map(\ String -> freshType(), vars)), a);
}

function maybeWrapTypePP
Document ::= a::Type
{
  return if a.wrapPP then pp"(${a.pp})" else a.pp;
}
