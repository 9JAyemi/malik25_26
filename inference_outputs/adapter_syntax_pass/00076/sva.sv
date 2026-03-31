module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] shift_amount,
    input logic shift_dir,
    input logic enable,
    input logic [1:0] select,
    input logic [15:0] out
);

    // No RTL clock or reset; clk is a sampling clock for these checks.

    // Left shift by 0 passes A through to the output.
    check_left_shift_by_zero_passthrough: assert property (
        @(posedge clk)
        (shift_dir && (shift_amount == 2'b00)) |-> (out == {12'b0, A})
    );

    // Left shift by 1 inserts a zero into bit 0.
    check_left_shift_by_one: assert property (
        @(posedge clk)
        (shift_dir && (shift_amount == 2'b01)) |-> (out == {11'b0, A[2:0], 1'b0})
    );

    // Left shift by 2 inserts two zeros into bits [1:0].
    check_left_shift_by_two: assert property (
        @(posedge clk)
        (shift_dir && (shift_amount == 2'b10)) |-> (out == {10'b0, A[1:0], 2'b00})
    );

    // Left shift by 3 inserts three zeros into bits [2:0].
    check_left_shift_by_three: assert property (
        @(posedge clk)
        (shift_dir && (shift_amount == 2'b11)) |-> (out == {9'b0, A[0], 3'b000})
    );

    // Right shift by 0 passes A through to the output.
    check_right_shift_by_zero_passthrough: assert property (
        @(posedge clk)
        (!shift_dir && (shift_amount == 2'b00)) |-> (out == {12'b0, A})
    );

    // Right shift by 1 inserts a zero into bit 3.
    check_right_shift_by_one: assert property (
        @(posedge clk)
        (!shift_dir && (shift_amount == 2'b01)) |-> (out == {1'b0, A[3:1], 3'b000})
    );

    // Right shift by 2 inserts two zeros into bits [3:2].
    check_right_shift_by_two: assert property (
        @(posedge clk)
        (!shift_dir && (shift_amount == 2'b10)) |-> (out == {2'b00, A[3:2], 4'b0000})
    );

    // Right shift by 3 inserts three zeros into bits [3:1].
    check_right_shift_by_three: assert property (
        @(posedge clk)
        (!shift_dir && (shift_amount == 2'b11)) |-> (out == {3'b000, A[3], 5'b00000})
    );

    // With enable low, the decoder contribution to out is zero.
    check_decoder_disabled_zero: assert property (
        @(posedge clk)
        (!enable) |-> (out[15:4] == 12'b0)
    );

    // With enable high, the decoder contribution is a one-hot nibble.
    check_decoder_enabled_onehot: assert property (
        @(posedge clk)
        enable |-> $onehot(out[15:12])
    );

    // The upper nibble of out is always zero.
    check_out_upper_nibble_zero: assert property (
        @(posedge clk)
        (out[15:4] == 12'b0)
    );

endmodule