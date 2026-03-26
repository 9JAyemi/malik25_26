module mux_4to2_sva (
    input logic clk,
    input logic X,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1
);

    // Output matches the implemented mux equation; A3 is unused.
    check_mux_equation: assert property (
        @(posedge clk) X == (S1 ? A2 : (S0 ? A1 : A0))
    );

    // When both selects are low, the output comes from A0.
    check_select_a0: assert property (
        @(posedge clk) (!S1 && !S0) |-> (X == A0)
    );

    // When S1 is low and S0 is high, the output comes from A1.
    check_select_a1: assert property (
        @(posedge clk) (!S1 && S0) |-> (X == A1)
    );

    // When S1 is high and S0 is low, the output comes from A2.
    check_select_a2_s0_low: assert property (
        @(posedge clk) (S1 && !S0) |-> (X == A2)
    );

    // When S1 is high and S0 is high, the output still comes from A2.
    check_select_a2_s0_high: assert property (
        @(posedge clk) (S1 && S0) |-> (X == A2)
    );

endmodule