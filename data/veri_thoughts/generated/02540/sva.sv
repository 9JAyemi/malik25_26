module sky130_fd_sc_ls__xor2_sva (
    input logic CLK,          // sampling clock for assertions
    input logic X,            // DUT output
    input logic A,            // DUT input
    input logic B,            // DUT input
    input logic xor0_out_X    // DUT internal net
);
    // DUT has no clock/reset; pure combinational XOR with output buffer.
    // Key behavior: X = A ^ B, with X buffered from xor0_out_X.

    // X must equal A XOR B.
    check_xor_equals_expr: assert property (
        @(posedge CLK) X == (A ^ B)
    );

    // Internal XOR output must equal A XOR B.
    check_internal_xor_equals_expr: assert property (
        @(posedge CLK) xor0_out_X == (A ^ B)
    );

    // Buffer must pass internal XOR output to X.
    check_buf_pass_through: assert property (
        @(posedge CLK) X == xor0_out_X
    );

    // Truth table: 00 -> 0.
    check_truth_00: assert property (
        @(posedge CLK) (A == 1'b0 && B == 1'b0) |-> (X == 1'b0)
    );

    // Truth table: 01 -> 1.
    check_truth_01: assert property (
        @(posedge CLK) (A == 1'b0 && B == 1'b1) |-> (X == 1'b1)
    );

    // Truth table: 10 -> 1.
    check_truth_10: assert property (
        @(posedge CLK) (A == 1'b1 && B == 1'b0) |-> (X == 1'b1)
    );

    // Truth table: 11 -> 0.
    check_truth_11: assert property (
        @(posedge CLK) (A == 1'b1 && B == 1'b1) |-> (X == 1'b0)
    );

    // When B is 0, X must equal A.
    check_b_zero_transparent: assert property (
        @(posedge CLK) (B == 1'b0) |-> (X == A)
    );

    // When B is 1, X must equal inverted A.
    check_b_one_inverts_a: assert property (
        @(posedge CLK) (B == 1'b1) |-> (X == ~A)
    );

    // When A is 0, X must equal B.
    check_a_zero_transparent: assert property (
        @(posedge CLK) (A == 1'b0) |-> (X == B)
    );

    // When A is 1, X must equal inverted B.
    check_a_one_inverts_b: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == ~B)
    );

endmodule