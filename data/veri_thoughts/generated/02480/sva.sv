module addsub32_sva (
    input logic CLK,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic op,
    input logic [31:0] R
);
    // R matches add/sub function based on op when op is known (LSB32 truncation).
    check_result_matches_op: assert property (
        @(posedge CLK) (!$isunknown(op)) |-> R == (op ? (A - B) : (A + B))[31:0]
    );

    // When op==0, R equals A+B (LSB32).
    check_add_path: assert property (
        @(posedge CLK) (op === 1'b0) |-> R == (A + B)[31:0]
    );

    // When op==1, R equals A-B (LSB32).
    check_sub_path: assert property (
        @(posedge CLK) (op === 1'b1) |-> R == (A - B)[31:0]
    );

    // For addition, R - B recovers A (mod 2^32).
    check_add_inverse_R_minus_B_eq_A: assert property (
        @(posedge CLK) (op === 1'b0) |-> (R - B)[31:0] == A
    );

    // For addition, R - A recovers B (mod 2^32).
    check_add_inverse_R_minus_A_eq_B: assert property (
        @(posedge CLK) (op === 1'b0) |-> (R - A)[31:0] == B
    );

    // For subtraction, R + B recovers A (mod 2^32).
    check_sub_inverse_R_plus_B_eq_A: assert property (
        @(posedge CLK) (op === 1'b1) |-> (R + B)[31:0] == A
    );

    // For subtraction, A - R recovers B (mod 2^32).
    check_sub_inverse_A_minus_R_eq_B: assert property (
        @(posedge CLK) (op === 1'b1) |-> (A - R)[31:0] == B
    );

    // For addition, commutativity holds: R equals B+A (LSB32).
    check_add_commutativity: assert property (
        @(posedge CLK) (op === 1'b0) |-> R == (B + A)[31:0]
    );

    // For addition, if B is zero, R passes A.
    check_add_zero_B_passthrough_A: assert property (
        @(posedge CLK) (op === 1'b0 && (B == 32'd0)) |-> R == A
    );

    // For subtraction, if A equals B, result is zero (LSB32).
    check_sub_A_eq_B_zero: assert property (
        @(posedge CLK) (op === 1'b1 && (A == B)) |-> R == 32'd0
    );
endmodule