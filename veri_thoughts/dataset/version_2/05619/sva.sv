module sky130_fd_sc_hs__udp_mux_4to2_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic X
);

    // X matches the implemented sum-of-products logic.
    check_full_equation: assert property (
        @(posedge clk) X == ((A0 & ~S0) | (A1 & S0) | (A2 & ~S1) | (A3 & S1))
    );

    // With both selects low, X is the OR of A0 and A2.
    check_sel_00: assert property (
        @(posedge clk) (!S0 && !S1) |-> (X == (A0 | A2))
    );

    // With S0 low and S1 high, X is the OR of A0 and A3.
    check_sel_01: assert property (
        @(posedge clk) (!S0 && S1) |-> (X == (A0 | A3))
    );

    // With S0 high and S1 low, X is the OR of A1 and A2.
    check_sel_10: assert property (
        @(posedge clk) (S0 && !S1) |-> (X == (A1 | A2))
    );

    // With both selects high, X is the OR of A1 and A3.
    check_sel_11: assert property (
        @(posedge clk) (S0 && S1) |-> (X == (A1 | A3))
    );

endmodule