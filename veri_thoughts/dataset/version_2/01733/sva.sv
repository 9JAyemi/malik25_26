module top_module_sva (
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_and_bitwise,
    input logic       out_and_logical,
    input logic [2:0] out_xor,
    input logic [5:0] out_not
);
    // No clock/reset in RTL; use posedge of $global_clock for sampling.

    // Bitwise AND output matches a & b.
    check_bitwise_and_def: assert property (
        @(posedge $global_clock) out_and_bitwise == (a & b)
    );

    // Logical AND output is 1 only when both a and b are non-zero.
    check_logical_and_def: assert property (
        @(posedge $global_clock) out_and_logical == ((a != 3'b000) && (b != 3'b000))
    );

    // XOR output matches a ^ b.
    check_xor_def: assert property (
        @(posedge $global_clock) out_xor == (a ^ b)
    );

    // Upper out_not bits are bitwise NOT of a.
    check_out_not_upper_def: assert property (
        @(posedge $global_clock) out_not[5:3] == ~a
    );

    // Lower out_not bits are bitwise NOT of b.
    check_out_not_lower_def: assert property (
        @(posedge $global_clock) out_not[2:0] == ~b
    );

    // When a equals b, XOR output is zero.
    check_xor_zero_when_equal: assert property (
        @(posedge $global_clock) (a == b) |-> (out_xor == 3'b000)
    );

    // If a is zero, bitwise AND output is zero.
    check_and_zero_if_a_zero: assert property (
        @(posedge $global_clock) (a == 3'b000) |-> (out_and_bitwise == 3'b000)
    );

    // If b is zero, bitwise AND output is zero.
    check_and_zero_if_b_zero: assert property (
        @(posedge $global_clock) (b == 3'b000) |-> (out_and_bitwise == 3'b000)
    );

    // If either input is zero, logical AND output is zero.
    check_logical_and_zero_if_any_zero: assert property (
        @(posedge $global_clock) ((a == 3'b000) || (b == 3'b000)) |-> (out_and_logical == 1'b0)
    );

    // If both inputs are non-zero, logical AND output is one.
    check_logical_and_one_if_both_nonzero: assert property (
        @(posedge $global_clock) ((a != 3'b000) && (b != 3'b000)) |-> (out_and_logical == 1'b1)
    );

endmodule