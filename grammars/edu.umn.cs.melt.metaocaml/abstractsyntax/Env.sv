grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

type Env = [Pair<String EnvItem>];
inherited attribute env::Env;
synthesized attribute polyVars::[String];
synthesized attribute defInQuote::Boolean;

nonterminal EnvItem with defInQuote, polyVars, type, freeVars;

abstract production envItem
top::EnvItem ::= inQuote::Boolean polyVars::[String] type::Type
{
  top.defInQuote = inQuote;
  top.polyVars = polyVars;
  top.type = type;
  propagate freeVars;
}

function envFreeVars
[String] ::= e::Env
{
  return unionsBy(stringEq, map((.freeVars), map(snd, e)));
}