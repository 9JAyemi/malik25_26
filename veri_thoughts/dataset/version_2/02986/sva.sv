module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    // Pure combinational logic; no clock/reset in RTL; sample on input edges.

    // X must equal (A1 & A2) | ~B1_N on any input edge.
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
            X == ((A1 & A2) | ~B1_N)
    );

    // When B1_N is LOW, X must be HIGH.
    check_low_B1N_forces_X_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
            (!B1_N) |-> (X == 1'b1)
    );

    // When B1_N is HIGH, X equals A1 & A2.
    check_high_B1N_equals_and: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
            (B1_N) |-> (X == (A1 & A2))
    );

    // If both A1 and A2 are HIGH, X must be HIGH.
    check_both_A_high_implies_X_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
            (A1 && A2) |-> (X == 1'b1)
    );

    // With B1_N HIGH and A1 LOW, X must be LOW.
    check_high_B1N_A1_low_implies_X_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
            (B1_N && !A1) |-> (X == 1'b0)
    );

    // With B1_N HIGH and A2 LOW, X must be LOW.
    check_high_B1N_A2_low_implies_X_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1_N or negedge B1_N)
            (B1_N && !A2) |-> (X == 1'b0)
    );

    // On B1_N falling edge, X must be HIGH due to ~B1_N term.
    check_B1N_fall_sets_X_high: assert property (
        @(negedge B1_N) X == 1'b1
    );

    // On B1_N rising edge, X equals A1 & A2.
    check_B1N_rise_sets_X_to_and: assert property (
        @(posedge B1_N) X == (A1 & A2)
    );

    // On A1 rising edge with B1_N HIGH and A2 HIGH, X must be HIGH.
    check_A1_rise_when_enabled_sets_X_high: assert property (
        @(posedge A1) (B1_N && A2) |-> (X == 1'b1)
    );

    // On A2 rising edge with B1_N HIGH and A1 HIGH, X must be HIGH.
    check_A2_rise_when_enabled_sets_X_high: assert property (
        @(posedge A2) (B1_N && A1) |-> (X == 1'b1)
    );

endmodule