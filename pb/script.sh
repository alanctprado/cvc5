#!bin/bash

for ((i = 4; i <= 20; i += 4)); do
	sed "s/SIZE/$i/" yoni.smt2 > test_file.smt2
	cat test_file.smt2
	rm test_file.smt2
done

