#!/bin/bash

# calculates delay propagation per cycle for comp.sv, and any child modules
# this includes memory
# so, SLOOWWWW!

set -ex
set -o pipefail

python verigpu/timing.py --in-verilog src/const.sv src/op_const.sv \
    src/assert_ignore.sv \
    src/float/float_params.sv src/float/float_add_pipeline.sv \
    src/int/chunked_add_task.sv src/int/chunked_sub_task.sv \
    src/generated/mul_pipeline_cycle_24bit_2bpc.sv src/float/float_mul_pipeline.sv \
    src/generated/mul_pipeline_cycle_32bit_2bpc.sv src/int/mul_pipeline_32bit.sv \
    src/int/int_div_regfile.sv \
    src/core.sv src/mem_small.sv src/global_mem_controller.sv \
    src/gpu_controller.sv \
    src/gpu_die.sv \
    --top-module gpu_die
