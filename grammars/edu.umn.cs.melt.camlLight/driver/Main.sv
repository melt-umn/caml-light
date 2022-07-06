grammar edu:umn:cs:melt:camlLight:driver;


imports edu:umn:cs:melt:camlLight:concreteSyntax;
imports edu:umn:cs:melt:camlLight:abstractSyntax;



parser hostparse::Root_c
{
  edu:umn:cs:melt:camlLight:concreteSyntax;
}

function main
IOVal<Integer> ::= largs::[String] ioin::IOToken
{
  local filename::String = head(largs);
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  local text::IOVal<String> = readFileT(filename, fileExists.io);
  local result::ParseResult<Root_c> = hostparse(text.iovalue, filename);

  local r_cst::Root_c = result.parseTree;
  local attribute r_ast::Root = r_cst.ast;

  local print_success::IOToken = printT(r_ast.output ++ "\n", text.io);

  return if null(largs)
         then ioval(printT("Filename not provided.\n", ioin), 1)
         else if !fileExists.iovalue
              then ioval(printT("File does not exist.\n",
                               fileExists.io), 1)
              else if !result.parseSuccess
                   then ioval(printT("Parse failed.\n" ++
                              result.parseErrors ++ "\n", text.io), 1)
                   else ioval(print_success, 0);
}


