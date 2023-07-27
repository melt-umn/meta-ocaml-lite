grammar edu:umn:cs:melt:metaocaml:driver;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:metaocaml:concretesyntax;
imports edu:umn:cs:melt:metaocaml:abstractsyntax;

parser parse::Expr_c {
  edu:umn:cs:melt:metaocaml:concretesyntax;
}

function eval
(String, Integer) ::= e::Expr
{
  e.inQuote = false;
  e.env = [];
  e.subsIn = [];
  e.subsFinal = e.subsOut;
  e.valueEnv = [];
  
  return
    if !null(e.errors)
    then (s"Errors:\n${messagesToString(e.errors)}\n", 4)
    else case e.value of
    | left(msg) -> (s"Runtime error:\n${msg.output}\n", 5)
    | right(v) -> (s"${show(80, v.pp)} : ${show(80, applySubs(e.subsFinal, e.type).pp)}\n", 0)
    end;
}

function main
IOVal<Integer> ::= args::[String] ioIn::IOToken
{
  local fileName :: String = head(args);
  local result::IO<Integer> = do {
    if length(args) != 1 then do {
      print("Usage: java -jar metaocaml.jar [file name]\n");
      return 1;
    } else do {
      isF::Boolean <- isFile(fileName);
      if !isF then do {
        print("File \"" ++ fileName ++ "\" not found.\n");
        return 2;
      } else do {
        text :: String <- readFile(fileName);
        let result :: ParseResult<Expr_c> = parse(text, fileName);
        if !result.parseSuccess then do {
          print(result.parseErrors ++ "\n");
          return 3;
        } else do {
          let ast::Expr = result.parseTree.ast;
          let result::(String, Integer) = eval(ast);
          print(result.fst);
          return result.snd;
        };
      };
    };
  };
  
  return evalIO(result, ioIn);
}
