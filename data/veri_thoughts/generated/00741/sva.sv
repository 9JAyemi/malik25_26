module sky130_fd_sc_hd__a2bb2oi_sva (
    input  logic CLK,
    input  logic Y,
    input  logic A1_N,
    input  logic A2_N,
    input  logic B1,
    input  logic B2
);
    ///// Combinational function checks /////
    // Functional equivalence to the gate structure: Y = ~(~(A1_N | A2_N) | (B1 & B2)).
    check_function_equation_direct: assert property (
        @(posedge CLK) Y == ~(~(A1_N | A2_N) | (B1 & B2))
    );

    // Same function via De Morgan: Y = (A1_N | A2_N) & (~B1 | ~B2).
    check_function_equation_demorgan: assert property (
        @(posedge CLK) Y == ((A1_N | A2_N) & ((~B1) | (~B2)))
    );

    // Both B inputs HIGH force Y LOW.
    check_both_B_high_forces_low: assert property (
        @(posedge CLK) (B1 & B2) |-> (Y == 1'b0)
    );

    // Both A_N inputs LOW force Y LOW.
    check_both_A_low_forces_low: assert property (
        @(posedge CLK) ((A1_N == 1'b0) && (A2_N == 1'b0)) |-> (Y == 1'b0)
    );

    // When not both B inputs are HIGH, Y equals (A1_N | A2_N).
    check_not_both_B_high_gives_A_or: assert property (
        @(posedge CLK) !(B1 & B2) |-> (Y == (A1_N | A2_N))
    );

    // If any A_N is HIGH and not both B are HIGH, Y is HIGH.
    check_A_or_and_not_B_and_implies_Y_high: assert property (
        @(posedge CLK) ((A1_N | A2_N) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // Y HIGH implies at least one A_N is HIGH and not both B are HIGH.
    check_Y_high_implies_conditions: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((A1_N | A2_N) && !(B1 & B2))
    );

    // Y LOW implies either both A_N are LOW or both B are HIGH.
    check_Y_low_implies_causes: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (!(A1_N | A2_N) || (B1 & B2))
    );

    // If inputs are stable across a cycle, Y must be stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) $stable({A1_N, A2_N, B1, B2}) |-> $stable(Y)
    );

    // If A1_N equals A2_N and not both B are HIGH, Y equals that common A_N value.
    check_equal_As_reduce_to_single: assert property (
        @(posedge CLK) ((A1_N == A2_N) && !(B1 & B2)) |-> (Y == A1_N)
    );

endmodule