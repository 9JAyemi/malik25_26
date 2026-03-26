module barrel_shifter_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [2:0] shift_amount,
    input logic shift_direction,
    input logic [7:0] data_out
);

    // RTL is combinational with no reset; clk is only a sampling clock for SVA.

    // Right-shift mode must match the RTL shift operation.
    check_right_shift_function: assert property (
        @(posedge clk) (shift_direction == 1'b0) |-> (data_out == (data_in >> shift_amount))
    );

    // Left-shift mode must match the RTL shift operation.
    check_left_shift_function: assert property (
        @(posedge clk) (shift_direction == 1'b1) |-> (data_out == (data_in << shift_amount))
    );

    // A zero shift must pass the input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) (shift_amount == 3'b000) |-> (data_out == data_in)
    );

    // Right shift by one must insert a zero into the MSB.
    check_right_shift_by_one: assert property (
        @(posedge clk) (shift_direction == 1'b0 && shift_amount == 3'b001) |-> (data_out == {1'b0, data_in[7:1]})
    );

    // Left shift by one must insert a zero into the LSB.
    check_left_shift_by_one: assert property (
        @(posedge clk) (shift_direction == 1'b1 && shift_amount == 3'b001) |-> (data_out == {data_in[6:0], 1'b0})
    );

    // Right shift by seven must leave only the original MSB.
    check_right_shift_by_seven: assert property (
        @(posedge clk) (shift_direction == 1'b0 && shift_amount == 3'b111) |-> (data_out == {7'b0, data_in[7]})
    );

    // Left shift by seven must leave only the original LSB.
    check_left_shift_by_seven: assert property (
        @(posedge clk) (shift_direction == 1'b1 && shift_amount == 3'b111) |-> (data_out == {data_in[0], 7'b0})
    );

    // Any non-zero right shift must zero-fill the MSB.
    check_right_shift_zero_fills_msb: assert property (
        @(posedge clk) (shift_direction == 1'b0 && shift_amount != 3'b000) |-> (data_out[7] == 1'b0)
    );

    // Any non-zero left shift must zero-fill the LSB.
    check_left_shift_zero_fills_lsb: assert property (
        @(posedge clk) (shift_direction == 1'b1 && shift_amount != 3'b000) |-> (data_out[0] == 1'b0)
    );

    // Stable inputs must produce a stable sampled output.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(data_in) && $stable(shift_amount) && $stable(shift_direction)) |-> $stable(data_out)
    );

endmodule