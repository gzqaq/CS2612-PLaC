%option noyywrap yylineno
%option outfile="lexer.c" header-file="lexer.h"
%{
#include "lang.h"
%}

%%

0|[1-9][0-9]* {
    val.n = build_nat(yytext, yyleng);
    print_token(TOK_NAT);
}

"var" {
    print_token(TOK_VAR);
}

"if" {
    print_token(TOK_IF);
}

"then" {
    print_token(TOK_THEN);
}

"else" {
    print_token(TOK_ELSE);
}

"while" {
    print_token(TOK_WHILE);
}

"do" {
    print_token(TOK_DO);
}

"malloc" {
    print_token(TOK_MALLOC);
}

"read_int" {
    print_token(TOK_RI);
}

"read_char" {
    print_token(TOK_RC);
}

"write_int" {
    print_token(TOK_WI);
}

"write_char" {
    print_token(TOK_WC);
}

[_A-Za-z][_A-Za-z0-9]* {
    val.i = new_str(yytext, yyleng);
    print_token(TOK_IDENT);
}

";" {
    print_token(TOK_SEMICOL);
    }

"(" {
    print_token(TOK_LEFT_PAREN);
    }

")" {
    print_token(TOK_RIGHT_PAREN);
    }

"{" {
    print_token(TOK_LEFT_BRACE);
    }

"}" {
    print_token(TOK_RIGHT_BRACE);
    }

"+" {
    print_token(TOK_PLUS);
    }

"-" {
    print_token(TOK_MINUS);
    }

"*" {
    print_token(TOK_MUL);
    }

"/" {
    print_token(TOK_DIV);
    }

"%" {
    print_token(TOK_MOD);
    }

"<" {
    print_token(TOK_LT);
    }

">" {
    print_token(TOK_GT);
    }

"<=" {
    print_token(TOK_LE);
    }

">=" {
    print_token(TOK_GE);
    }

"==" {
    print_token(TOK_EQ);
    }

"!=" {
    print_token(TOK_NE);
    }

"=" {
    print_token(TOK_ASGNOP);
    }

"&&" {
    print_token(TOK_AND);
    }

"||" {
    print_token(TOK_OR);
    }

"!" {
    print_token(TOK_NOT);
    }

[ \t\n\r]    { };

.   {printf("%s",yytext);
     return -1; }
%%
