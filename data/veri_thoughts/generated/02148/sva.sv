module arithmetic_op_sva (
    input logic clk,          // Clock for sampling assertions
    input logic [3:0] Y,      // DUT output
    input logic [3:0] A,      // DUT input
    input logic [3:0] B,      // DUT input
    input logic S             // DUT select
);

    // When S==0, Y equals A + B (4-bit wraparound).
    check_add_result_when_S0: assert property (
        @(posedge clk) (S == 1'b0) |-> (Y == (A + B))
    );

    // When S==1, Y equals A - B (4-bit wraparound).
    check_sub_result_when_S1: assert property (
        @(posedge clk) (S == 1'b1) |-> (Y == (A - B))
    );

    // If inputs A, B, S are stable, Y must remain stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(S)) |-> $stable(Y)
    );

    // If B is zero, Y must equal A regardless of S.
    check_passthrough_when_B_zero: assert property (
        @(posedge clk) (B == 4'h0) |-> (Y == A)
    );

    // For subtraction with equal operands, result is zero.
    check_zero_when_A_eq_B_and_sub: assert property (
        @(posedge clk) (S == 1'b1 && A == B) |-> (Y == 4'h0)
    );

    // Inverse identity for addition: (A+B)-B == A.
    check_add_inverse_identity: assert property (
        @(posedge clk) (S == 1'b0) |-> ((Y - B) == A)
    );

    // Inverse identity for subtraction: (A-B)+B == A.
    check_sub_inverse_identity: assert property (
        @(posedge clk) (S == 1'b1) |-> ((Y + B) == A)
    );

    // On S rising edge with stable A,B, Y reflects subtraction.
    check_y_on_rose_S_with_inputs_stable: assert property (
        @(posedge clk) ($rose(S) && $stable(A) && $stable(B)) |-> (Y == (A - B))
    );

    // On S falling edge with stable A,B, Y reflects addition.
    check_y_on_fell_S_with_inputs_stable: assert property (
        @(posedge clk) ($fell(S) && $stable(A) && $stable(B)) |-> (Y == (A + B))
    );

    // When adding equal operands, result LSB must be 0 (2*A mod 16 is even).
    check_even_result_when_S0_and_A_eq_B: assert property (
        @(posedge clk) (S == 1'b0 && A == B) |-> (Y[0] == 1'b0)
    );

endmodule