all: pigeon_itauto.dat

pigeon_hole.vo : pigeon_hole.v
	coqc pigeon_hole.v

%.dat: %.v pigeon_hole.v
	ulimit -Sv 15000000; $(COQBIN)/coqc $< | cut -d' ' -f4 > $@

%.qed: %.dat
	sed '1d;n; d' $< > $@

%.tac: %.dat
	sed 'n; d' $< > $@

%dat2: %dat Makefile
	cat $< | grep "Tactic call" | grep "success" > $@

#gnuplot --persist
pigeon_qed.pdf : pigeon_itauto.qed pigeon_tauto.qed pigeon_rtauto.qed plot_qed
	gnuplot -s plot_qed

pigeon_tac.pdf : pigeon_itauto.tac pigeon_tauto.tac pigeon_rtauto.tac plot_tac
	gnuplot -s plot_tac


compcert.tac1 compcert.tac2 compcert.tac : compcert.dat2 Makefile
	cat $< | grep -e "^Lia" -e "^Tauto" -e "T1"  > compcert.tac1
	cat $< | grep -e "^ILia" -e "^ITauto" -e "T2" > compcert.tac2
	paste compcert.tac2 compcert.tac1 > compcert.tac


bedrock2.tac1 bedrock2.tac2 bedrock2.tac : bedrock2.dat2 Makefile
	cat $< | grep -e "^Lia" -e "^Tauto" -e "T1"  > bedrock2.tac1
	cat $< | grep -e "^ILia" -e "^ITauto" -e "T2" > bedrock2.tac2
	paste bedrock2.tac2 bedrock2.tac1 > bedrock2.tac


compcert.pdf : compcert.tac1 compcert.tac2 compcert.tac plot_compcert
	gnuplot -s plot_compcert

bedrock2.pdf : bedrock2.tac1 bedrock2.tac2 bedrock2.tac plot_bedrock2
	gnuplot -s plot_bedrock2


cmp : compare.ml
	ocamlfind ocamlc -o cmp  -package str -linkpkg compare.ml

clean:
	rm *pdf
