#!/bin/bash

CVC5_BIN="/home/alan/logic/cvc5/build/bin/cvc5"

dir_path="$(pwd)/implemented"

# Sanity check
for FILE in "$dir_path"/*; do
    bb_result=$("$CVC5_BIN" "$FILE")
    pb_result=$("$CVC5_BIN" "$FILE" --bv-solver=pb-blast --bv-pb-solver=roundingsat)

if [ "$bb_result" != "$pb_result" ]; then
    echo "ERROR!!"
    echo "BB and PB results are different for file $FILE"
        exit 1
    fi

done

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

# Compare approaches
bb_times=()
pb_times=()
for FILE in "$dir_path"/*; do
    bb_result=$( { time $CVC5_BIN "$FILE"; } 2>&1 )
    pb_result=$( { time $CVC5_BIN "$FILE" --bv-solver=pb-blast --bv-pb-solver=roundingsat; } 2>&1 )
    bb_times+=("$(get_time "$bb_result"),")
    pb_times+=("$(get_time "$pb_result"),")
done

echo "bb_result = [${bb_times[@]}]"
echo "pb_result = [${pb_times[@]}]"




#    if [ $exit_code -eq 0 ]; then
#        mv "$FILE" "$implemented_dir"
#        echo "Moved $FILE to $implemented_dir"
#    else
#        mv "$FILE" "$unimplemented_dir"
#        echo "Moved $FILE to $unimplemented_dir"
#    fi
