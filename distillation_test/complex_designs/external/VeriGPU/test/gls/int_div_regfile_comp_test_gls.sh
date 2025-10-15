#!/bin/bash

# run gate-level simulation on src/int_div_regfile.sv, as part of entire proc, comp etc

set -ex
set -o pipefail

prog=test_divu_modu_mul

python verigpu/assembler.py --in-asm examples/direct/${prog}.asm --out-hex build/build.hex
cat test/behav/core_and_mem_driver.sv | sed -e "s/{PROG}/build/g" > build/core_and_mem_driver.sv

# first output gate-level netlists for int_div_regfile.sv
python verigpu/run_yosys.py --in-verilog src/const.sv \
    src/assert_ignore.sv src/int/int_div_regfile.sv --top-module int_div_regfile >/dev/null

# now try running with proc, comp etc
iverilog -g2012 tech/osu018/osu018_stdcells.v build/netlist/6.v src/const.sv \
    src/assert_ignore.sv src/mem_large.sv \
    src/generated/mul_pipeline_cycle_24bit_2bpc.sv src/float/float_mul_pipeline.sv \
    src/int/chunked_add_task.sv src/int/chunked_sub_task.sv \
    src/generated/mul_pipeline_cycle_32bit_2bpc.sv src/int/mul_pipeline_32bit.sv \
    src/float/float_params.sv src/float/float_add_pipeline.sv \
    src/op_const.sv src/core.sv src/global_mem_controller.sv \
    test/behav/core_and_mem.sv test/behav/core_and_mem_driver.sv

./a.out
