module shift_register_sva (
    input logic clk,
    input logic shift_dir,
    input logic parallel_load,
    input logic [7:0] data_in,
    input logic [7:0] serial_out,
    input logic [7:0] parallel_out
);

// parallel_load captures data_in into the register on the next cycle.
    check_parallel_load_captures_data: assert property (
        @(posedge clk) parallel_load |=> (parallel_out == $past(data_in))
    );

// parallel_load has priority over shift_dir when both are high.
    check_parallel_load_priority_over_shift: assert property (
        @(posedge clk) (parallel_load && shift_dir) |=> (parallel_out == $past(data_in))
    );

// shift_dir=1 rotates the register left by one bit and inserts 0 into bit 0.
    check_left_shift_rotates: assert property (
        @(posedge clk) (!parallel_load && shift_dir) |=> (parallel_out == {$past(parallel_out[6:0]), 1'b0})
    );

// shift_dir=0 rotates the register right by one bit and inserts 0 into bit 7.
    check_right_shift_rotates: assert property (
        @(posedge clk) (!parallel_load && !shift_dir) |=> (parallel_out == {1'b0, $past(parallel_out[7:1])})
    );

// serial_out reflects the LSB of the register on the next cycle.
    check_serial_out_is_lsb: assert property (
        @(posedge clk) 1'b1 |=> (serial_out == $past(parallel_out[0]))
    );

// A left shift moves bits [6:0] into [7:1] and inserts 0 into bit 0.
    check_left_shift_data_mapping: assert property (
        @(posedge clk) (!parallel_load && shift_dir) |=> (parallel_out[7:1] == $past(parallel_out[6:0]))
    );

// A right shift moves bits [7:1] into [6:0] and inserts 0 into bit 7.
    check_right_shift_data_mapping: assert property (
        @(posedge clk) (!parallel_load && !shift_dir) |=> (parallel_out[6:0] == $past(parallel_out[7:1]))
    );

// A left shift leaves the previous MSB (bit 7) as 0.
    check_left_shift_inserts_zero_msb: assert property (
        @(posedge clk) (!parallel_load && shift_dir) |=> (parallel_out[7] == 1'b0)
    );

// A right shift leaves the previous LSB (bit 0) as 0.
    check_right_shift_inserts_zero_lsb: assert property (
        @(posedge clk) (!parallel_load && !shift_dir) |=> (parallel_out[0] == 1'b0)
    );

endmodule
