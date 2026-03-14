module sky130_fd_sc_lp__a22oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    ///// Functional equivalence /////
    // Y implements ~( (A1 & A2) | (B1 & B2) ) sampled on A1 rising edge.
    check_y_function_equivalence: assert property (
        @(posedge A1) Y == ~((A1 & A2) | (B1 & B2))
    );

    // If A1&A2 are both HIGH, Y must be LOW.
    check_y_low_when_A_pair_high: assert property (
        @(posedge A1) (A1 & A2) |-> (Y == 1'b0)
    );

    // If B1&B2 are both HIGH, Y must be LOW.
    check_y_low_when_B_pair_high: assert property (
        @(posedge A1) (B1 & B2) |-> (Y == 1'b0)
    );

    // If neither A1&A2 nor B1&B2 are HIGH, Y must be HIGH.
    check_y_high_when_neither_pair_high: assert property (
        @(posedge A1) (!(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );
endmodule