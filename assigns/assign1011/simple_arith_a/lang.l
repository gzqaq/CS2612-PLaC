%option noyywrap yylineno
%option outfile="lexer.c" header-file="lexer.h"
%{
  #include "lang.h"
  #include "parser.h"
%}

%%

0|[1-9][0-9]* {
  yylval.n = build_nat(yytext, yyleng);
  return TM_NAT;
}

[_A-Za-z][_A-Za-z0-9]* {
  yylval.i = new_str(yytext, yyleng);
  return TM_ID;
}

"(" {
  return TM_LEFT_PAREN;
}

")" {
  return TM_RIGHT_PAREN;
}

"+" {
  return TM_PLUS;
}

"*" {
  return TM_MUL;
}

[ \t\n\r] { };

. {
  printf("%s", yytext);
  return -1;
}

%%