module sky130_fd_sc_hdll__nor2b_sva (
    input logic Y,
    input logic A,
    input logic B_N
);
    ///// Functional equivalence: Y = (~A) & B_N /////
    // Y equals (~A & B_N) at A rising edge.
    check_func_posedge_A: assert property (
        @(posedge A) Y == ((~A) & B_N)
    );
    // Y equals (~A & B_N) at A falling edge.
    check_func_negedge_A: assert property (
        @(negedge A) Y == ((~A) & B_N)
    );
    // Y equals (~A & B_N) at B_N rising edge.
    check_func_posedge_BN: assert property (
        @(posedge B_N) Y == ((~A) & B_N)
    );
    // Y equals (~A & B_N) at B_N falling edge.
    check_func_negedge_BN: assert property (
        @(negedge B_N) Y == ((~A) & B_N)
    );

    ///// Necessary conditions for Y transitions /////
    // Y can be HIGH only when A is LOW and B_N is HIGH.
    check_y_rise_requires_inputs: assert property (
        @(posedge Y) (A == 1'b0) && (B_N == 1'b1)
    );
    // If A is HIGH, Y must be LOW.
    check_A_high_forces_Y_low: assert property (
        @(posedge B_N) (A == 1'b1) |-> (Y == 1'b0)
    );
    // If B_N is LOW, Y must be LOW.
    check_BN_low_forces_Y_low: assert property (
        @(posedge A) (B_N == 1'b0) |-> (Y == 1'b0)
    );

    ///// Directional effects on output with specific input edges /////
    // With B_N HIGH, Y equals NOT A (sampled on A edge).
    check_BN_high_implies_Y_eq_notA: assert property (
        @(posedge A) (B_N == 1'b1) |-> (Y == (~A))
    );
    // A rising with B_N HIGH causes Y to fall.
    check_y_fall_on_A_rise_when_BN_high: assert property (
        @(posedge A) (B_N == 1'b1) |-> $fell(Y)
    );
    // B_N rising with A LOW causes Y to rise.
    check_y_rise_on_BN_rise_when_A_low: assert property (
        @(posedge B_N) (A == 1'b0) |-> $rose(Y)
    );
endmodule