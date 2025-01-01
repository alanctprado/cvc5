#!bin/bash

for ((i = 2; i <= 12; i += 2)); do
	repeat=$(printf '10%.0s' $(seq 1 $((i / 2))))
	sed "s/SIZE/$i/" ineq1.smt2 | sed "s/DOUBLE/$((i * 2))/" | sed "s/CONSTANT/$repeat/" > test_file.smt2
	echo $i
	[ $i -eq 10 ] && cp test_file.smt2 ineq1-10.smt2
	../build/bin/cvc5 test_file.smt2 --bv-solver=pb-blast --bv-pb-solver=roundingsat
	rm test_file.smt2
done

