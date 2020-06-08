all : CoqMakefile
	make -f CoqMakefile

install :
	make -f CoqMakefile install

clean :
	make -f CoqMakefile clean

CoqMakefile : _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

