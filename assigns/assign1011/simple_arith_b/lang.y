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
%type <e> NT_E

// Priority
%left TM_PLUS
%left TM_MUL
%left TM_LEFT_PAREN TM_RIGHT_PAREN

%%

NT_WHOLE:
  NT_E {
    $$ = ($1);
    root = $$;
  }
;

NT_E:
  NT_E TM_PLUS NT_E {
    $$ = (TPlus($1, $3));
  }
| NT_E TM_MUL NT_E {
    $$ = (TMult($1, $3));
  }
| TM_LEFT_PAREN NT_E TM_RIGHT_PAREN {
    $$ = ($2);
  }
| TM_NAT {
    $$ = (TConst($1));
  }
| TM_ID {
    $$ = (TVar($1));
  }
;

%%

void yyerror(char * s) {
  fprintf(stderr, "%s\n", s);
}