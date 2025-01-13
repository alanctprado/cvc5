#!/bin/bash

CVC5_BIN="/home/alan/logic/cvc5/build/bin/cvc5"
TEST_FILE="$(pwd)/test_file.smt2"

filename="$1"
if [[ -z "$filename" ]]; then
  echo "Usage: $0 <filename>"
  exit 1
fi

file_path="$(pwd)/$filename"
echo "Processing file: $file_path"

get_time() {
    local cvc5_time_output="$1"
	local real_time
	local minutes
	local seconds
	local milliseconds
	local total_milliseconds

	real_time=$(echo "$cvc5_time_output" | grep real | tr -s '[:space:]' ',' | cut -d',' -f2)

	minutes=$(echo "$real_time" | cut -d'm' -f1)
	seconds=$(echo "$real_time" | cut -d'm' -f2 | cut -d'.' -f1)
	milliseconds=$(echo "$real_time" | cut -d'm' -f2 | cut -d'.' -f2 | tr -d 's')

    total_milliseconds=$(echo "($minutes * 60 + $seconds) * 1000 + $milliseconds" | bc)
	echo "$total_milliseconds"
}

bb_times=()
pb_times=()
for ((i = 2; i <= 16; i += 2)); do
#	sed "s/SIZE/$i/" "$file_path" > test_file.smt2
	repeat=$(printf '10%.0s' $(seq 1 $((i / 2))))
	sed "s/SIZE/$i/" "$file_path" | sed "s/DOUBLE/$((i * 2))/" | sed "s/CONSTANT/$repeat/" > "$TEST_FILE"

	bb_result=$( { time $CVC5_BIN "$TEST_FILE"; } 2>&1 )
	pb_result=$( { time $CVC5_BIN "$TEST_FILE" --bv-solver=pb-blast --bv-pb-solver=roundingsat; } 2>&1 )

	if [ "$(echo "$bb_result" | head -n1)" != "$(echo "$pb_result" | head -n1)" ]; then
		echo "ERROR!!"
		echo "BB and PB results are different for bit-width $i"
		exit 1
	fi

	bb_times+=("($i, $(get_time "$bb_result")),")
	pb_times+=("($i, $(get_time "$pb_result")),")

	rm "$TEST_FILE"
done

echo "Problem: $filename"
echo "bb_result = [${bb_times[@]}]"
echo "pb_result = [${pb_times[@]}]"

