grammar grammars:driver;


imports grammars:concreteSyntax;
imports grammars:abstractSyntax;



parser hostparse::Root_c
{
  grammars:concreteSyntax;
}

function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local filename::String = head(largs);
  local fileExists::IOVal<Boolean> = isFile(filename, ioin);
  local text::IOVal<String> = readFile(filename, fileExists.io);
  local result::ParseResult<Root_c> = hostparse(text.iovalue, filename);

  local r_cst::Root_c = result.parseTree;
  local attribute r_ast::Root = r_cst.ast;

  local print_success::IO = print(r_ast.output ++ "\n", text.io);

  return if null(largs)
         then ioval(print("Filename not provided.\n", ioin), 1)
         else if !fileExists.iovalue
              then ioval(print("File does not exist.\n",
                               fileExists.io), 1)
              else if !result.parseSuccess
                   then ioval(print("Parse failed.\n" ++
                              result.parseErrors ++ "\n", text.io), 1)
                   else ioval(print_success, 0);
}


