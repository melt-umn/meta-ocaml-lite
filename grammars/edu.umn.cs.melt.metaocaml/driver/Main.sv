grammar edu:umn:cs:melt:metaocaml:driver;

imports core:monad;
imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:metaocaml:concretesyntax;
imports edu:umn:cs:melt:metaocaml:abstractsyntax;

parser parse::Expr_c {
  edu:umn:cs:melt:metaocaml:concretesyntax;
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
          case decorate ast with {valueEnv = [];}.value of
          | left(msg) -> printM("Error: " ++ msg ++ "\n")
          | right(v) -> printM(show(80, v.pp) ++ "\n")
          end;
          return 0;
        }
      }
    }
  };
  
  return evalIO(result, ioIn);
}
