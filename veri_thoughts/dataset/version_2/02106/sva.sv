module sky130_fd_sc_hdll__o21bai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    ///// Combinational function checks (sampled on any input edge) /////
    // Y implements ~(~B1_N & (A1 | A2)).
    check_functional_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        Y == ~(~B1_N & (A1 | A2))
    );

    // If B1_N is HIGH, Y must be HIGH.
    check_b1n_high_forces_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        (B1_N == 1'b1) |-> (Y == 1'b1)
    );

    // If B1_N is LOW and A1 is HIGH, Y must be LOW.
    check_b1n_low_a1_high_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        ((B1_N == 1'b0) && (A1 == 1'b1)) |-> (Y == 1'b0)
    );

    // If B1_N is LOW and A2 is HIGH, Y must be LOW.
    check_b1n_low_a2_high_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        ((B1_N == 1'b0) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // If A1 and A2 are both LOW, Y must be HIGH.
    check_both_a_low_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // Y LOW implies B1_N is LOW and at least one of A1/A2 is HIGH.
    check_y_low_implies_conditions: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        (Y == 1'b0) |-> ((B1_N == 1'b0) && (A1 || A2))
    );

    // If B1_N is LOW and Y is HIGH, then A1 and A2 are both LOW.
    check_b1n_low_y_high_implies_both_a_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        ((B1_N == 1'b0) && (Y == 1'b1)) |-> ((A1 == 1'b0) && (A2 == 1'b0))
    );

    // If (A1 or A2) is HIGH, Y must equal B1_N.
    check_or_high_y_equals_b1n: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        (A1 || A2) |-> (Y == B1_N)
    );

    // With B1_N LOW and A2 LOW, Y equals ~A1.
    check_b1n_low_a2_low_y_eq_not_a1: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        ((B1_N == 1'b0) && (A2 == 1'b0)) |-> (Y == ~A1)
    );

    // With B1_N LOW and A1 LOW, Y equals ~A2.
    check_b1n_low_a1_low_y_eq_not_a2: assert property (
        @(posedge A1 or posedge A2 or posedge B1_N or
          negedge A1 or negedge A2 or negedge B1_N)
        disable iff (1'b0)
        ((B1_N == 1'b0) && (A1 == 1'b0)) |-> (Y == ~A2)
    );
endmodule