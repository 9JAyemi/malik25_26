module mux4to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S0,
    input logic S1,
    input logic Y
);

    // Y matches the RTL sum-of-products expression.
    check_output_equation: assert property (
        @(posedge clk)
        Y == ((A & ~S0 & ~S1) | (B & ~S0 & S1) | (A & S0 & ~S1) | (B & S0 & S1))
    );

    // When S1 is low, Y follows A.
    check_select_a_when_s1_low: assert property (
        @(posedge clk)
        (S1 == 1'b0) |-> (Y == A)
    );

    // When S1 is high, Y follows B.
    check_select_b_when_s1_high: assert property (
        @(posedge clk)
        (S1 == 1'b1) |-> (Y == B)
    );

    // Changing only S0 does not affect Y.
    check_s0_has_no_effect: assert property (
        @(posedge clk)
        !$initstate && $changed(S0) && $stable(A) && $stable(B) && $stable(S1) |-> $stable(Y)
    );

    // With S1 low, the unselected B input does not affect Y.
    check_b_unselected_when_s1_low: assert property (
        @(posedge clk)
        !$initstate && (S1 == 1'b0) && $changed(B) && $stable(A) && $stable(S0) && $stable(S1) |-> $stable(Y)
    );

    // With S1 high, the unselected A input does not affect Y.
    check_a_unselected_when_s1_high: assert property (
        @(posedge clk)
        !$initstate && (S1 == 1'b1) && $changed(A) && $stable(B) && $stable(S0) && $stable(S1) |-> $stable(Y)
    );

    // If A and B are equal, Y equals that common value.
    check_equal_inputs_same_output: assert property (
        @(posedge clk)
        (A == B) |-> (Y == A)
    );

endmodule