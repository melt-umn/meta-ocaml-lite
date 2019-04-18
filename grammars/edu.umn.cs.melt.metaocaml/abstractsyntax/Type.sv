grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

synthesized attribute type::Type;

synthesized attribute wrapPP::Boolean;

type Subs = [Pair<String Type>];
inherited attribute subsIn::Subs;
synthesized attribute subsOut::Subs;
autocopy attribute subsFinal::Subs;

autocopy attribute unifyWith::Type;
synthesized attribute unify::Maybe<Subs>;
synthesized attribute substituted::Type;

synthesized attribute freshened::Type;

nonterminal Type with pp, wrapPP, unifyWith, unify, subsFinal, substituted, subsIn, subsOut, freshened;

abstract production errorType
top::Type ::=
{
  propagate substituted, freshened;
  top.pp = pp"<err>";
  top.wrapPP = false;
  top.unify = just([]);
  top.subsOut = top.subsIn;
}

abstract production varType
top::Type ::= n::String
{
  top.pp = pp"'${text(n)}";
  top.wrapPP = false;
  top.unify = just([pair(n, top.unifyWith)]);
  top.substituted =
    case lookupBy(stringEq, n, top.subsFinal) of
    | just(a) -> applySubs(top.subsFinal, a)
    | nothing() -> top
    end;
  
  local f::Type = freshType();
  top.subsOut =
    case lookupBy(stringEq, n, top.subsIn) of
    | just(_) -> top.subsIn
    | nothing() -> pair(n, f) :: top.subsIn
    end;
  top.freshened =
    case lookupBy(stringEq, n, top.subsIn) of
    | just(a) -> a
    | nothing() -> f
    end;
}

abstract production skolemType
top::Type ::= n::String
{
  propagate substituted;
  top.pp = pp"'${text(n)}";
  top.wrapPP = false;
  top.unify =
    case top.unifyWith of
    | errorType() -> just([])
    | skolemType(n1) -> if n == n1 then just([]) else nothing()
    | varType(n1) -> just([pair(n1, top)])
    | _ -> nothing()
    end;
  
  local f::Type = freshType();
  top.subsOut =
    case lookupBy(stringEq, n, top.subsIn) of
    | just(_) -> top.subsIn
    | nothing() -> pair(n, f) :: top.subsIn
    end;
  top.freshened =
    case lookupBy(stringEq, n, top.subsIn) of
    | just(a) -> a
    | nothing() -> f
    end;
}

abstract production intType
top::Type ::=
{
  propagate substituted, freshened;
  top.pp = pp"int";
  top.wrapPP = false;
  top.unify =
    case top.unifyWith of
    | errorType() -> just([])
    | intType() -> just([])
    | varType(n) -> just([pair(n, top)])
    | _ -> nothing()
    end;
  top.subsOut = top.subsIn;
}

abstract production boolType
top::Type ::=
{
  propagate substituted, freshened;
  top.pp = pp"bool";
  top.wrapPP = false;
  top.unify =
    case top.unifyWith of
    | errorType() -> just([])
    | boolType() -> just([])
    | varType(n) -> just([pair(n, top)])
    | _ -> nothing()
    end;
  top.subsOut = top.subsIn;
}

abstract production functionType
top::Type ::= a::Type b::Type
{
  propagate substituted, freshened;
  top.pp = pp"${maybeWrapTypePP(a)} -> ${maybeWrapTypePP(b)}";
  top.wrapPP = true;
  top.unify =
    case top.unifyWith of
    | errorType() -> just([])
    | functionType(a1, b1) ->
      do (bindMaybe, returnMaybe) {
        s1::Subs <- unify(a, a1);
        s2::Subs <- unify(b, b1);
        return s1 ++ s2;
      }
    | varType(n) -> just([pair(n, top)])
    | _ -> nothing()
    end;
  a.subsIn = top.subsIn;
  b.subsIn = a.subsOut;
  top.subsOut = b.subsOut;
}

abstract production codeType
top::Type ::= a::Type
{
  propagate substituted, freshened;
  top.pp = pp"${maybeWrapTypePP(a)} code";
  top.wrapPP = true;
  top.unify =
    case top.unifyWith of
    | errorType() -> just([])
    | codeType(a1) -> unify(a, a1)
    | varType(n) -> just([pair(n, top)])
    | _ -> nothing()
    end;
  a.subsIn = top.subsIn;
  top.subsOut = a.subsOut;
}

nonterminal Check with subsIn, subsOut, subsFinal, errors;

abstract production typeCheck
top::Check ::= a::Type b::Type loc::Location
{
  local newSubs::Maybe<Subs> = 
    do (bindMaybe, returnMaybe) {
      s1::Subs <- unify(applySubs(top.subsIn, a), applySubs(top.subsIn, b));
      return s1 ++ top.subsIn;
    };
  top.subsOut = fromMaybe(top.subsIn, newSubs);
  local finalA::Type = applySubs(top.subsFinal, a);
  local finalB::Type = applySubs(top.subsFinal, b);
  top.errors :=
    if newSubs.isJust
    then []
    else [err(loc, s"Incompatible types ${show(80, finalA.pp)} and ${show(80, finalB.pp)}")];
}

function freshType
Type ::=
{
  return varType("a" ++ toString(genInt()));
}

function unify
Maybe<Subs> ::= a::Type b::Type
{
  a.unifyWith = b;
  return a.unify;
}

function applySubs
Type ::= s::Subs t::Type
{
  t.subsFinal = s;
  return t.substituted;
}

function freshenType
Type ::= a::Type
{
  a.subsIn = [];
  return a.freshened;
}

function maybeWrapTypePP
Document ::= a::Type
{
  return if a.wrapPP then pp"(${a.pp})" else a.pp;
}
