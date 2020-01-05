grammar edu:umn:cs:melt:metaocaml:driver;

imports core:monad;
imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:metaocaml:concretesyntax;
imports edu:umn:cs:melt:metaocaml:abstractsyntax;

parser parse::Expr_c {
  edu:umn:cs:melt:metaocaml:concretesyntax;
}

function eval
Pair<String Integer> ::= e::Expr
{
  e.inQuote = false;
  e.env = [];
  e.subsIn = [];
  e.subsFinal = e.subsOut;
  e.valueEnv = [];
  
  return
    if !null(e.errors)
    then pair(s"Errors:\n${messagesToString(e.errors)}\n", 4)
    else case e.value of
    | left(msg) -> pair(s"Runtime error:\n${msg.output}\n", 5)
    | right(v) -> pair(s"${show(80, v.pp)} : ${show(80, applySubs(e.subsFinal, e.type).pp)}\n", 0)
    end;
}

function main
IOVal<Integer> ::= args::[String] ioIn::IO
{
  local fileName :: String = head(args);
  local result::IOMonad<Integer> = do (bindIO, returnIO) {
    if length(args) != 1 then {
      printM("Usage: java -jar metaocaml.jar [file name]\n");
      return 1;
    } else {
      isF::Boolean <- isFileM(fileName);
      if !isF then {
        printM("File \"" ++ fileName ++ "\" not found.\n");
        return 2;
      } else {
        text :: String <- readFileM(fileName);
        result :: ParseResult<Expr_c> = parse(text, fileName);
        if !result.parseSuccess then {
          printM(result.parseErrors ++ "\n");
          return 3;
        } else {
          ast::Expr = result.parseTree.ast;
          result::Pair<String Integer> = eval(ast);
          printM(result.fst);
          return result.snd;
        }
      }
    }
  };
  
  return evalIO(result, ioIn);
}
