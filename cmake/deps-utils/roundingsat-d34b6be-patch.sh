#!/bin/sh

awk '
# Update the branch used
/GIT_BRANCH "unknown"/ {
    gsub(/unknown/, "main")
}

# Update the commit used
/COMMIT_HASH "unknown"/ {
    gsub(/unknown/, "d34b6be")
}

# Do not print the lines between these two matches
# (inclusive for the first line and exclusive for
# the last).
/# Get the current working branch/ {
    flag = 1;
    next
}

/add_definitions\("-DGIT_COMMIT_HASH/ {
    flag = 0
}

!flag
' $1 > tmp-roundingsat-patch

mv tmp-roundingsat-patch $1
