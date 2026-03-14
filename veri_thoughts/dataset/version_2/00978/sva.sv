module sky130_fd_sc_hd__o2bb2ai_sva (
    input logic clk,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    ///// Combinational function checks /////
    // Y equals (A1_N & A2_N) | (~B1 & ~B2).
    check_truth_function_sop: assert property (
        @(posedge clk) Y == ((A1_N & A2_N) | (~B1 & ~B2))
    );

    // Y equals ~(~(A2_N & A1_N) & (B1 | B2)).
    check_truth_function_demorgan: assert property (
        @(posedge clk) Y == ~(~(A2_N & A1_N) & (B1 | B2))
    );

    ///// Input-driven behavior /////
    // When both B inputs are 0, Y must be 1.
    check_y_high_when_no_b: assert property (
        @(posedge clk) (B1 == 1'b0 && B2 == 1'b0) |-> (Y == 1'b1)
    );

    // When B1 is 1, Y equals A1_N & A2_N.
    check_y_eq_aand_when_b1_high: assert property (
        @(posedge clk) (B1 == 1'b1) |-> (Y == (A1_N & A2_N))
    );

    // When B2 is 1, Y equals A1_N & A2_N.
    check_y_eq_aand_when_b2_high: assert property (
        @(posedge clk) (B2 == 1'b1) |-> (Y == (A1_N & A2_N))
    );

    // If any B is 1 and A1_N is 0, Y must be 0.
    check_y_low_when_a1_low_and_any_b: assert property (
        @(posedge clk) ((B1 | B2) && (A1_N == 1'b0)) |-> (Y == 1'b0)
    );

    // If any B is 1 and A2_N is 0, Y must be 0.
    check_y_low_when_a2_low_and_any_b: assert property (
        @(posedge clk) ((B1 | B2) && (A2_N == 1'b0)) |-> (Y == 1'b0)
    );

    // If both A_N inputs are 1, Y must be 1.
    check_y_high_when_a_both_high: assert property (
        @(posedge clk) ((A1_N & A2_N) == 1'b1) |-> (Y == 1'b1)
    );

    // If Y is 0, then some B is 1 and not both A_N are 1.
    check_y_zero_implication: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((B1 | B2) && (~(A1_N & A2_N)))
    );
endmodule