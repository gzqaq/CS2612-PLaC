all: main

lang.o: lang.c lang.h
	clang -c lang.c

lexer.c: lang.l
	flex lang.l

lexer.o: lexer.c lang.h
	clang -c lexer.c

main.o: main.c lang.h lexer.c
	clang -c main.c

main: main.o lang.o lexer.o
	clang main.o lang.o lexer.o -o main

clean:
	rm -f *.o lexer.c lexer.h main
