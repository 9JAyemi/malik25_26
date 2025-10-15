#!/bin/bash

set -e
set -x

run_verilog() {
    $1 | tee /tmp/out.txt
    set +x
    if grep ERROR /tmp/out.txt; then {
        echo "ERROR"
        exit 1
    } fi
    set -x
}

run_verilog test/behav/float/float_add_pipeline_test.sh
run_verilog test/behav/float/float_test_funcs_test.sh
run_verilog test/behav/int/int_div_regfile_test.sh
run_verilog test/behav/int/int_div_regfile_comp_test.sh
run_verilog test/behav/mem_delayed_test.sh

echo "PASS"
