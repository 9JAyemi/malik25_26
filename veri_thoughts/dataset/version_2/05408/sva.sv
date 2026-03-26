module custom_op_sva (
    input logic        clk,
    input logic [15:0] in_value,
    input logic [15:0] mask_value,
    input logic [3:0]  shift_value,
    input logic [2:0]  op_select,
    input logic [15:0] out_value
);

    // AND selection produces a bitwise AND.
    check_and_result: assert property (
        @(posedge clk) (op_select == 3'b000) |-> (out_value == (in_value & mask_value))
    );

    // OR selection produces a bitwise OR.
    check_or_result: assert property (
        @(posedge clk) (op_select == 3'b001) |-> (out_value == (in_value | mask_value))
    );

    // XOR selection produces a bitwise XOR.
    check_xor_result: assert property (
        @(posedge clk) (op_select == 3'b010) |-> (out_value == (in_value ^ mask_value))
    );

    // Left-shift selection shifts by shift_value.
    check_left_shift_result: assert property (
        @(posedge clk) (op_select == 3'b011) |-> (out_value == (in_value << shift_value))
    );

    // Right-shift selection shifts by shift_value.
    check_right_shift_result: assert property (
        @(posedge clk) (op_select == 3'b100) |-> (out_value == (in_value >> shift_value))
    );

    // Unused op_select values pass the input through.
    check_default_passthrough: assert property (
        @(posedge clk) ((op_select == 3'b101) || (op_select == 3'b110) || (op_select == 3'b111)) |-> (out_value == in_value)
    );

    // Left shift by zero leaves the input unchanged.
    check_left_shift_zero_identity: assert property (
        @(posedge clk) ((op_select == 3'b011) && (shift_value == 4'h0)) |-> (out_value == in_value)
    );

    // Right shift by zero leaves the input unchanged.
    check_right_shift_zero_identity: assert property (
        @(posedge clk) ((op_select == 3'b100) && (shift_value == 4'h0)) |-> (out_value == in_value)
    );

    // AND with a zero mask yields zero.
    check_and_zero_mask: assert property (
        @(posedge clk) ((op_select == 3'b000) && (mask_value == 16'h0000)) |-> (out_value == 16'h0000)
    );

    // OR with a zero mask leaves the input unchanged.
    check_or_zero_mask_identity: assert property (
        @(posedge clk) ((op_select == 3'b001) && (mask_value == 16'h0000)) |-> (out_value == in_value)
    );

    // XOR with a zero mask leaves the input unchanged.
    check_xor_zero_mask_identity: assert property (
        @(posedge clk) ((op_select == 3'b010) && (mask_value == 16'h0000)) |-> (out_value == in_value)
    );

endmodule