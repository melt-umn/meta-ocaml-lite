grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

type Env = [(String, EnvItem)];
inherited attribute env::Env;
synthesized attribute polyVars::[String];
synthesized attribute defInQuote::Boolean;

nonterminal EnvItem with defInQuote, polyVars, type, freeVars;

abstract production envItem
top::EnvItem ::= inQuote::Boolean polyVars::[String] type::Type
{
  top.defInQuote = inQuote;
  top.polyVars = polyVars;
  top.type = ^type;
  propagate freeVars;
}

fun envFreeVars [String] ::= e::Env = unions(map((.freeVars), map(snd, e)));