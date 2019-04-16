grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

autocopy attribute valueEnv::[Pair<String Value>];
synthesized attribute value::Either<String Value>;

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
