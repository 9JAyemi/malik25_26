#!/bin/bash

set -ex

iverilog -g2012 src/const.sv src/assert.sv src/int/int_div_regfile.sv test/behav/int/int_div_regfile_test.sv
./a.out
