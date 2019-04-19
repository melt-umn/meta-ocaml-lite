grammar edu:umn:cs:melt:metaocaml:abstractsyntax;

autocopy attribute env::[Pair<String EnvItem>];
synthesized attribute defInQuote::Boolean;

nonterminal EnvItem with defInQuote, type;

abstract production envItem
top::EnvItem ::= inQuote::Boolean type::Type
{
  top.defInQuote = inQuote;
  top.type = type;
}
