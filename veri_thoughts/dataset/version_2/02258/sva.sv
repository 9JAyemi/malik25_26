module binary_adder_sva (
    // DUT ports as inputs
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,

    // External clock for sampling combinational behavior (DUT has no clock/reset)
    input logic CLK
);

    ///// Functional correctness (mod-16 addition) /////
    // S equals the low 4 bits of the 5-bit sum of A and B (mod-16 sum).
    check_sum_mod16: assert property (
        @(posedge CLK) S == ({1'b0, A} + {1'b0, B})[3:0]
    );

    // When no carry from A+B, S equals the plain 4-bit sum.
    check_no_carry_case: assert property (
        @(posedge CLK) (({1'b0, A} + {1'b0, B}) <= 5'd15) |-> (S == (A + B))
    );

    // When there is a carry from A+B, S equals (A+B-16) modulo 16.
    check_with_carry_case: assert property (
        @(posedge CLK) (({1'b0, A} + {1'b0, B}) > 5'd15) |-> (S == (({1'b0, A} + {1'b0, B} - 5'd16)[3:0]))
    );

    ///// Identity and special cases /////
    // Adding zero on B leaves S == A.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 4'd0) |-> (S == A)
    );

    // Adding zero on A leaves S == B.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 4'd0) |-> (S == B)
    );

    // 8 + 8 = 16 wraps to 0.
    check_8_plus_8_wraps: assert property (
        @(posedge CLK) ((A == 4'd8) && (B == 4'd8)) |-> (S == 4'd0)
    );

    // 15 + 1 wraps to 0.
    check_15_plus_1_wraps: assert property (
        @(posedge CLK) ((A == 4'd15) && (B == 4'd1)) |-> (S == 4'd0)
    );

    // If A is 15, result equals (B - 1) modulo 16.
    check_A_is_15: assert property (
        @(posedge CLK) (A == 4'd15) |-> (S == (B - 4'd1))
    );

    // If B is 15, result equals (A - 1) modulo 16.
    check_B_is_15: assert property (
        @(posedge CLK) (B == 4'd15) |-> (S == (A - 4'd1))
    );

    ///// Stability /////
    // If inputs are stable, output is stable (pure combinational behavior).
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(S)
    );

    ///// Doubling special case /////
    // When A == B, S equals (2*A) modulo 16.
    check_A_equals_B_double: assert property (
        @(posedge CLK) (A == B) |-> (S == ({1'b0, A} << 1)[3:0])
    );

endmodule