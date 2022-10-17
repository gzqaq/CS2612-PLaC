%{
  #include <stdio.h>
  #include "lang.h" 
  #include "lexer.h"

  void yyerror(char *);
  int yylex(void);

  struct expr * root;
%}

%union {
  unsigned int n;  // store NAT
  char * i;  // store ID
  struct expr * e;
  void * none;
}

// Terminals
%token <n> TM_NAT
%token <i> TM_ID
%token <none> TM_LEFT_PAREN TM_RIGHT_PAREN
%token <none> TM_PLUS TM_MUL

// Nonterminals
%type <e> NT_WHOLE
%type <e> NT_E NT_F NT_G

%%

NT_WHOLE:
  NT_E {
    $$ = ($1);
    root = $$;
  }
;

NT_E:
  NT_F {
    $$ = ($1);
  }
| NT_E TM_PLUS NT_F {
    $$ = (TPlus($1, $3));
  }
;

NT_F:
  NT_G {
    $$ = ($1);
  }
| NT_F TM_MUL NT_G {
    $$ = (TMult($1, $3));
  }
;

NT_G:
  TM_LEFT_PAREN NT_E TM_RIGHT_PAREN {
    $$ = ($2);
  }
| TM_ID {
    $$ = (TVar($1));
  }
| TM_NAT {
    $$ = (TConst($1));
  }
;

%%

void yyerror(char * s) {
  fprintf(stderr, "%s\n", s);
}